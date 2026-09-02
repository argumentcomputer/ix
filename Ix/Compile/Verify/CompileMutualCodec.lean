import Ix.Compile.Verify.CompileInductiveCodec

/-!
# Production mutual-block/codec bridge

The mutual driver compiles every member of each alpha-equivalence class but
emits payload and sharing roots only for the first member.  This module first
closes the mutual `Ind` compiler against the same proof-visible constructor
fold used by standalone inductives; the class and block folds build on that
common boundary below.
-/

namespace Ix.Compile.Verify

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α)
    (next : α → Ix.CompileM.CompileM β) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (action >>= next) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state action with
      | .error err => .error err
      | .ok (value, state') =>
        Ix.CompileM.CompileM.run compileEnv blockEnv state' (next value) := by
  simp [Ix.CompileM.CompileM.run, ReaderT.run_bind, ExceptT.run_bind,
    StateT.run_bind]
  generalize
    (ReaderT.run action (compileEnv, blockEnv)).run.run state = result
  rcases result with ⟨result, state'⟩
  cases result <;> rfl

private theorem run_pure (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (value : α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (pure value) =
      .ok (value, state) := by
  rfl

private theorem run_throw (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (err : Ix.CompileM.CompileError) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (throw err :
      Ix.CompileM.CompileM α) = .error err := by
  rfl

private theorem run_withMutCtx (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (mutCtx : Ix.MutCtx) (action : Ix.CompileM.CompileM α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.withMutCtx mutCtx action) =
      Ix.CompileM.CompileM.run compileEnv
        { blockEnv with mutCtx := mutCtx } state action := by
  rfl

def compiledInductiveDataPayload (inductiveData : Ix.Ind)
    (typeExpr : Ixon.Expr) (ctors : Array Ixon.Constructor) :
    Ixon.Inductive :=
  { isUnsafe := inductiveData.isUnsafe
    lvls := inductiveData.levelParams.size.toUInt64
    params := inductiveData.numParams.toUInt64
    indices := inductiveData.numIndices.toUInt64
    typ := typeExpr
    ctors }

private def inductiveDataMutNames (blockEnv : Ix.CompileM.BlockEnv) :
    Array Ix.Name :=
  blockEnv.mutCtx.toList.toArray.map (·.1)

private def inductiveDataMutCtxAddrs (blockEnv : Ix.CompileM.BlockEnv) :
    Array Address :=
  blockEnv.mutCtx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map
      (·.1.getHash)

/-- The mutual `Ind` finalizer preserves the primary expression tables and
assembles exactly the captured type metadata and ordered constructor fold. -/
theorem finishInductiveDataCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveData : Ix.Ind)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeMeta : Ix.CompileM.InductiveTypeCompileMeta)
    (compiledCtors : Ix.CompileM.InductiveConstructorCompileState) :
    ∃ indMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishInductiveDataCompilation inductiveData typeExpr
            typeRoot typeMeta compiledCtors) =
        .ok ((compiledInductiveDataPayload inductiveData typeExpr
            compiledCtors.ctors, indMeta, compiledCtors.ctorMetaPairs,
            compiledCtors.ctorExprs), state') ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.canonUnivCache = state.canonUnivCache := by
  let afterName := state.compileName inductiveData.name
  let afterLevels := afterName.compileNames inductiveData.levelParams
  let afterAll := afterLevels.compileNames inductiveData.all
  let mutNames := inductiveDataMutNames blockEnv
  let state' := afterAll.compileNames mutNames
  let ctxAddrs := inductiveDataMutCtxAddrs blockEnv
  let indMeta := { Ixon.ConstantMeta.new
      (.indc inductiveData.name.getHash
        (inductiveData.levelParams.map (·.getHash))
        compiledCtors.ctorNameAddrs
        (inductiveData.all.map (·.getHash)) ctxAddrs typeMeta.arena
        typeRoot) with
      metaSharing := typeMeta.surgerySharing
      metaUnivs := typeMeta.metaUnivs
      univPatches := typeMeta.univPatches }
  have hname := MetaStateFrame.compileName state inductiveData.name
  have hlevels := MetaStateFrame.compileNames afterName
    inductiveData.levelParams
  have hall := MetaStateFrame.compileNames afterLevels inductiveData.all
  have hmut := MetaStateFrame.compileNames afterAll mutNames
  have hframe := hname.trans <| hlevels.trans <| hall.trans hmut
  refine ⟨indMeta, state', ?_, ?_, hframe.exprCache,
    hframe.canonUnivCache⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterAll :=
        BlockState.compileNames_exprTableView afterAll mutNames
      _ = exprTableView afterLevels :=
        BlockState.compileNames_exprTableView afterLevels inductiveData.all
      _ = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          inductiveData.levelParams
      _ = exprTableView state :=
        (MetaStateFrame.compileName state inductiveData.name).tables

def inductiveDataCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (inductiveData : Ix.Ind) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := inductiveData.name
    univCtx := inductiveData.levelParams.toList }

theorem compileInductiveData_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveData : Ix.Ind) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileInductiveData inductiveData) =
      Ix.CompileM.CompileM.run compileEnv
        (inductiveDataCompileBlockEnv blockEnv inductiveData)
        (axiomCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr inductiveData.type
          let typeMeta ← Ix.CompileM.takeInductiveTypeCompileMeta
          let compiledCtors ← Ix.CompileM.compileInductiveConstructors
            inductiveData.ctors.toList { ctorExprs := #[typeExpr] }
          Ix.CompileM.finishInductiveDataCompilation inductiveData typeExpr
            typeRoot typeMeta compiledCtors) := by
  rfl

/-- Sequential ordinary compilation of a mutual inductive member preserves
the frozen preseed tables and produces a wire-safe payload and root array. -/
theorem compileInductiveData_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (inductiveData : Ix.Ind)
    {state : Ix.CompileM.BlockState}
    (htypeSource : SupportedOrdinaryExpr levelSupport inductiveData.type)
    (hctorSources : ∀ ctor ∈ inductiveData.ctors.toList,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type)
    (htypeBound : ExprWireBound inductiveData.type)
    (hctorBounds : ∀ ctor ∈ inductiveData.ctors.toList,
      ExprWireBound ctor.cnst.type)
    (hctorCount : inductiveData.ctors.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (inductiveDataCompileBlockEnv blockEnv inductiveData) levelSupport
      snapshot (axiomCompileStartState state))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveDataCompileBlockEnv blockEnv inductiveData) snapshot)
      inductiveData.type = some typeTarget)
    (hctorRefs : ∀ ctor ∈ inductiveData.ctors.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (inductiveDataCompileBlockEnv blockEnv inductiveData) snapshot)
        ctor.cnst.type = some target) :
    ∃ ind indMeta ctorMetaPairs ctorExprs state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveData inductiveData) =
        .ok ((ind, indMeta, ctorMetaPairs, ctorExprs), state') ∧
      BlockWireTablesWF state' ∧
      exprTableView state' = exprTableView snapshot ∧
      ind.wireWF ∧
      ExprArrayWireWF ctorExprs ∧
      state'.exprCache = {} ∧
      CanonUnivCacheWF state' := by
  let indEnv := inductiveDataCompileBlockEnv blockEnv inductiveData
  obtain ⟨typeTarget, htypeRef⟩ := htypeRef
  obtain ⟨typeRoot, typeState, htypeRun, htypeState, htypeWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv indEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htypeSource htypeBound hstate
      htypeRef
  let typeMeta := capturedInductiveTypeMeta typeState
  let ctorStart := inductiveConstructorPhaseState typeState
  have htake : Ix.CompileM.CompileM.run compileEnv indEnv typeState
      Ix.CompileM.takeInductiveTypeCompileMeta =
        .ok (typeMeta, ctorStart) := by
    exact takeInductiveTypeCompileMeta_run compileEnv indEnv typeState
  have hctorStart : FrozenExprStateWF compileEnv indEnv levelSupport
      snapshot ctorStart :=
    inductiveConstructorPhaseState_frozen compileEnv indEnv levelSupport
      snapshot typeState htypeState
  obtain ⟨compiledCtors, ctorState, hctorsRun, hctorState, hctorSize,
      hctorsWire, hrootsWire, hctorCache⟩ :=
    compileInductiveConstructors_run_ordinary_wireWF compileEnv indEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful
      inductiveData.ctors.toList
      ({ ctorExprs := #[typeTarget] } :
        Ix.CompileM.InductiveConstructorCompileState)
      hctorSources hctorBounds hctorRefs hctorStart rfl (by simp)
      (by
        intro expr hmem
        have heq : expr = typeTarget := by simpa using hmem
        subst expr
        exact htypeWire)
  obtain ⟨indMeta, state', hfinish, htablesFrame, hexprCache,
      hcanonCache⟩ :=
    finishInductiveDataCompilation_run compileEnv indEnv ctorState
      inductiveData typeTarget typeRoot typeMeta compiledCtors
  let ind := compiledInductiveDataPayload inductiveData typeTarget
    compiledCtors.ctors
  have hcompiledSize : compiledCtors.ctors.size =
      inductiveData.ctors.size := by
    simpa using hctorSize
  have hindWire : ind.wireWF := by
    refine ⟨htypeWire, ?_, ?_⟩
    · simpa [ind, compiledInductiveDataPayload, hcompiledSize] using
        hctorCount
    · intro ctor hmem
      exact hctorsWire ctor hmem
  have htableEq : exprTableView state' = exprTableView snapshot :=
    htablesFrame.trans hctorState.tables
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq htableEq
  refine ⟨ind, indMeta, compiledCtors.ctorMetaPairs,
    compiledCtors.ctorExprs, state', ?_, htables', htableEq, hindWire, hrootsWire,
    hexprCache.trans hctorCache,
    hctorState.canonUnivCache.of_cache_eq hcanonCache⟩
  rw [compileInductiveData_run_eq, run_bind, htypeRun]
  simp only
  rw [run_bind, htake]
  simp only
  rw [run_bind, hctorsRun]
  exact hfinish

/-! ## Equivalence-class member fold -/

/-- One independently compiled member has a wire-safe retained payload and
wire-safe roots. Metadata is intentionally outside the constant codec. -/
structure CompiledMutConstMemberWireWF
    (member : Ix.CompileM.CompiledMutConstMember) : Prop where
  payload : member.payload.wireWF
  roots : ExprArrayWireWF member.roots

/-- Every retained payload and sharing root in a mutual-fold accumulator is
inside the public wire domain. -/
structure MutConstCompileStateWireWF
    (state : Ix.CompileM.MutConstCompileState) : Prop where
  payloads : ∀ payload ∈ state.payloads, payload.wireWF
  roots : ExprArrayWireWF state.roots

theorem MutConstCompileStateWireWF.empty :
    MutConstCompileStateWireWF {} := by
  constructor <;> intro value hmem
  · exact (Array.not_mem_empty value hmem).elim
  · exact (Array.not_mem_empty value hmem).elim

private theorem exprArrayWireWF_append
    {left right : Array Ixon.Expr}
    (hleft : ExprArrayWireWF left) (hright : ExprArrayWireWF right) :
    ExprArrayWireWF (left ++ right) := by
  intro expr hmem
  simp only [Array.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hleft expr hmem
  · exact hright expr hmem

theorem MutConstCompileStateWireWF.addRepresentative
    {state : Ix.CompileM.MutConstCompileState}
    {member : Ix.CompileM.CompiledMutConstMember}
    (hstate : MutConstCompileStateWireWF state)
    (hmember : CompiledMutConstMemberWireWF member) :
    MutConstCompileStateWireWF (state.addRepresentative member) := by
  constructor
  · intro payload hmem
    simp only [Ix.CompileM.MutConstCompileState.addRepresentative,
      Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate.payloads payload hmem
    · exact hmember.payload
  · exact exprArrayWireWF_append hstate.roots hmember.roots

theorem MutConstCompileStateWireWF.addEquivalent
    {state : Ix.CompileM.MutConstCompileState}
    (member : Ix.CompileM.CompiledMutConstMember)
    (hstate : MutConstCompileStateWireWF state) :
    MutConstCompileStateWireWF (state.addEquivalent member) := by
  exact ⟨hstate.payloads, hstate.roots⟩

/-- A reusable preservation contract for one source member. The outer fold is
parametric in the live-state invariant, so the heterogeneous preseed theorem
can supply the concrete frozen-table invariant without duplicating list
reasoning. -/
def MutConstMemberRunWireReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (StateInv : Ix.CompileM.BlockState → Prop)
    (source : Ix.MutConst) : Prop :=
  ∀ state, StateInv state →
    ∃ member state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConstMember source) =
        .ok (member, state') ∧
      StateInv state' ∧
      CompiledMutConstMemberWireWF member

/-- Context-independent live-state invariant between mutual members. Every
member installs its own current name and universe parameters before compiling,
so only the frozen primary tables, empty expression cache, and canonical memo
must survive at the class-fold boundary. -/
structure MutualMemberStateWF
    (snapshot state : Ix.CompileM.BlockState) : Prop where
  tables : exprTableView state = exprTableView snapshot
  exprCache : state.exprCache = {}
  canonUnivCache : CanonUnivCacheWF state

theorem MutualMemberStateWF.axiomCompileStartState_frozen
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : MutualMemberStateWF snapshot state)
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (levelSupport : Ix.Level → Prop) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (axiomCompileStartState state) := by
  refine {
    tables := axiomCompileStartState_exprTableView state |>.trans
      hstate.tables
    exprCache := ?_
    univCache := ?_
    canonUnivCache := hstate.canonUnivCache.of_cache_eq rfl }
  · apply OrdinaryExprCacheWF.of_cache_eq
      (OrdinaryExprCacheWF.empty
        (frozenRefCompileCtx compileEnv blockEnv snapshot))
    exact hstate.exprCache
  · apply UnivCacheWF.of_cache_eq
      (UnivCacheWF.empty (univParamIndex blockEnv.univCtx) levelSupport)
    rfl

theorem MutualMemberStateWF.definitionCompileStartState_frozen
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : MutualMemberStateWF snapshot state)
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (levelSupport : Ix.Level → Prop) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (definitionCompileStartState state) := by
  simpa [axiomCompileStartState, definitionCompileStartState] using
    hstate.axiomCompileStartState_frozen compileEnv blockEnv levelSupport

/-- Ordinary-source obligations for a mutual definition-like member. -/
structure MutualDefinitionReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState)
    (levelSupport : Ix.Level → Prop) (definitionData : Ix.Def) : Prop where
  typeSource : SupportedOrdinaryExpr levelSupport definitionData.type
  valueSource : SupportedOrdinaryExpr levelSupport definitionData.value
  typeBound : ExprWireBound definitionData.type
  valueBound : ExprWireBound definitionData.value
  typeRef : ∃ target, compileExprRef
    (frozenRefCompileCtx compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
    definitionData.type = some target
  valueRef : ∃ target, compileExprRef
    (frozenRefCompileCtx compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
    definitionData.value = some target

/-- Ordinary-source obligations for a mutual inductive member. -/
structure MutualInductiveReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState)
    (levelSupport : Ix.Level → Prop) (inductiveData : Ix.Ind) : Prop where
  typeSource : SupportedOrdinaryExpr levelSupport inductiveData.type
  ctorSources : ∀ ctor ∈ inductiveData.ctors.toList,
    SupportedOrdinaryExpr levelSupport ctor.cnst.type
  typeBound : ExprWireBound inductiveData.type
  ctorBounds : ∀ ctor ∈ inductiveData.ctors.toList,
    ExprWireBound ctor.cnst.type
  ctorCount : inductiveData.ctors.size < UInt64.size
  typeRef : ∃ target, compileExprRef
    (frozenRefCompileCtx compileEnv
      (inductiveDataCompileBlockEnv blockEnv inductiveData) snapshot)
    inductiveData.type = some target
  ctorRefs : ∀ ctor ∈ inductiveData.ctors.toList, ∃ target,
    compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveDataCompileBlockEnv blockEnv inductiveData) snapshot)
      ctor.cnst.type = some target

/-- Ordinary-source obligations for a mutual recursor member. -/
structure MutualRecursorReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState)
    (levelSupport : Ix.Level → Prop)
    (recursorVal : Ix.RecursorVal) : Prop where
  typeSource : SupportedOrdinaryExpr levelSupport recursorVal.cnst.type
  ruleSources : ∀ rule ∈ recursorVal.rules.toList,
    SupportedOrdinaryExpr levelSupport rule.rhs
  typeBound : ExprWireBound recursorVal.cnst.type
  ruleBounds : ∀ rule ∈ recursorVal.rules.toList,
    ExprWireBound rule.rhs
  ruleCount : recursorVal.rules.size < UInt64.size
  typeRef : ∃ target, compileExprRef
    (frozenRefCompileCtx compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
    recursorVal.cnst.type = some target
  ruleRefs : ∀ rule ∈ recursorVal.rules.toList, ∃ target,
    compileExprRef
      (frozenRefCompileCtx compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
      rule.rhs = some target

/-- The source-side disjunction matching the three production mutual member
variants. -/
inductive MutConstOrdinaryReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState)
    (levelSupport : Ix.Level → Prop) : Ix.MutConst → Prop where
  | defn {definitionData : Ix.Def} :
      MutualDefinitionReady compileEnv blockEnv snapshot levelSupport
        definitionData →
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport
        (.defn definitionData)
  | indc {inductiveData : Ix.Ind} :
      MutualInductiveReady compileEnv blockEnv snapshot levelSupport
        inductiveData →
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport
        (.indc inductiveData)
  | recr {recursorVal : Ix.RecursorVal} :
      MutualRecursorReady compileEnv blockEnv snapshot levelSupport
        recursorVal →
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport
        (.recr recursorVal)

/-- Source-side wire/count obligations not supplied by preseed readiness.
For inductives, constructor parameter arrays must agree with the inherited
family context used by `compileInductiveData`. -/
inductive MutConstOrdinaryBounds : Ix.MutConst → Prop where
  | defn {definitionData : Ix.Def} :
      ExprWireBound definitionData.type →
      ExprWireBound definitionData.value →
      MutConstOrdinaryBounds (.defn definitionData)
  | indc {inductiveData : Ix.Ind} :
      ExprWireBound inductiveData.type →
      (∀ ctor ∈ inductiveData.ctors.toList,
        ExprWireBound ctor.cnst.type) →
      inductiveData.ctors.size < UInt64.size →
      (∀ ctor ∈ inductiveData.ctors.toList,
        ctor.cnst.levelParams.toList = inductiveData.levelParams.toList) →
      MutConstOrdinaryBounds (.indc inductiveData)
  | recr {recursorVal : Ix.RecursorVal} :
      ExprWireBound recursorVal.cnst.type →
      (∀ rule ∈ recursorVal.rules.toList, ExprWireBound rule.rhs) →
      recursorVal.rules.size < UInt64.size →
      MutConstOrdinaryBounds (.recr recursorVal)

/-- Member-local form of the common universe-parameter condition sufficient
to make the block's heterogeneous preseed traversal collision-safe.  An
inductive additionally records the constructor contexts that production
preseeding reads directly. -/
inductive MutConstUniformPreseedParams (params : List Ix.Name) :
    Ix.MutConst → Prop where
  | defn {definitionData : Ix.Def} :
      definitionData.levelParams.toList = params →
      MutConstUniformPreseedParams params (.defn definitionData)
  | indc {inductiveData : Ix.Ind} :
      inductiveData.levelParams.toList = params →
      (∀ ctor ∈ inductiveData.ctors.toList,
        ctor.cnst.levelParams.toList = params) →
      MutConstUniformPreseedParams params (.indc inductiveData)
  | recr {recursorVal : Ix.RecursorVal} :
      recursorVal.cnst.levelParams.toList = params →
      MutConstUniformPreseedParams params (.recr recursorVal)

theorem MutConstUniformPreseedParams.input
    {params : List Ix.Name} {source : Ix.MutConst}
    (huniform : MutConstUniformPreseedParams params source)
    {input : Ix.Expr × List Ix.Name}
    (hinput : input ∈ Ix.CompileM.mutConstPreseedInputs source) :
    input.2 = params := by
  cases huniform with
  | @defn definitionData hparams =>
      simp only [Ix.CompileM.mutConstPreseedInputs, List.mem_cons,
        List.not_mem_nil, or_false] at hinput
      rcases hinput with rfl | rfl <;> exact hparams
  | @indc inductiveData hparams hctors =>
      simp only [Ix.CompileM.mutConstPreseedInputs, List.mem_cons,
        List.mem_map] at hinput
      rcases hinput with rfl | ⟨ctor, hctor, rfl⟩
      · exact hparams
      · exact hctors ctor hctor
  | @recr recursorVal hparams =>
      simp only [Ix.CompileM.mutConstPreseedInputs, List.mem_map] at hinput
      obtain ⟨source, _hsource, rfl⟩ := hinput
      exact hparams

theorem mutConstClassPreseedInputs_uniform
    (params : List Ix.Name) (sources : List Ix.MutConst)
    (hmembers : ∀ source ∈ sources,
      MutConstUniformPreseedParams params source) :
    ∀ input ∈ Ix.CompileM.mutConstClassPreseedInputs sources,
      input.2 = params := by
  induction sources with
  | nil => simp [Ix.CompileM.mutConstClassPreseedInputs]
  | cons source rest ih =>
      intro input hinput
      simp only [Ix.CompileM.mutConstClassPreseedInputs,
        List.mem_append] at hinput
      rcases hinput with hsource | hrest
      · exact (hmembers source (by simp)).input hsource
      · apply ih
        · intro member hmem
          exact hmembers member (by simp [hmem])
        · exact hrest

theorem mutualPreseedInputs_uniform
    (params : List Ix.Name) (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstUniformPreseedParams params source) :
    ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      input.2 = params := by
  induction classes with
  | nil => simp [Ix.CompileM.mutualPreseedInputs]
  | cons constClass rest ih =>
      intro input hinput
      simp only [Ix.CompileM.mutualPreseedInputs, List.mem_append] at hinput
      rcases hinput with hclass | hrest
      · exact mutConstClassPreseedInputs_uniform params constClass
          (fun source hsource => hmembers constClass (by simp) source
            hsource) input hclass
      · apply ih
        · intro memberClass hclass source hsource
          exact hmembers memberClass (by simp [hclass]) source hsource
        · exact hrest

theorem mutConstPreseedInputs_mem_class
    {source : Ix.MutConst} {sources : List Ix.MutConst}
    (hsource : source ∈ sources) {input : Ix.Expr × List Ix.Name}
    (hinput : input ∈ Ix.CompileM.mutConstPreseedInputs source) :
    input ∈ Ix.CompileM.mutConstClassPreseedInputs sources := by
  induction sources with
  | nil => simp at hsource
  | cons head rest ih =>
      simp only [List.mem_cons] at hsource
      simp only [Ix.CompileM.mutConstClassPreseedInputs,
        List.mem_append]
      rcases hsource with rfl | hsource
      · exact Or.inl hinput
      · exact Or.inr (ih hsource)

theorem mutConstClassPreseedInputs_mem_mutual
    {constClass : List Ix.MutConst}
    {classes : List (List Ix.MutConst)}
    (hclass : constClass ∈ classes)
    {input : Ix.Expr × List Ix.Name}
    (hinput : input ∈
      Ix.CompileM.mutConstClassPreseedInputs constClass) :
    input ∈ Ix.CompileM.mutualPreseedInputs classes := by
  induction classes with
  | nil => simp at hclass
  | cons head rest ih =>
      simp only [List.mem_cons] at hclass
      simp only [Ix.CompileM.mutualPreseedInputs, List.mem_append]
      rcases hclass with rfl | hclass
      · exact Or.inl hinput
      · exact Or.inr (ih hclass)

theorem mutConstPreseedInputs_mem_mutual
    {classes : List (List Ix.MutConst)}
    {constClass : List Ix.MutConst} (hclass : constClass ∈ classes)
    {source : Ix.MutConst} (hsource : source ∈ constClass)
    {input : Ix.Expr × List Ix.Name}
    (hinput : input ∈ Ix.CompileM.mutConstPreseedInputs source) :
    input ∈ Ix.CompileM.mutualPreseedInputs classes :=
  mutConstClassPreseedInputs_mem_mutual hclass
    (mutConstPreseedInputs_mem_class hsource hinput)

/-- Frozen targets returned for one member's exact preseed inputs, together
with the residual source bounds, construct the member compiler's ordinary
readiness package. -/
theorem MutConstOrdinaryBounds.ready_of_preseed
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    {source : Ix.MutConst}
    (hbound : MutConstOrdinaryBounds source)
    (hsources : ∀ input ∈ Ix.CompileM.mutConstPreseedInputs source,
      SupportedOrdinaryExpr levelSupport input.1)
    (htargets : ∀ input ∈ Ix.CompileM.mutConstPreseedInputs source,
      ∃ target, compileExprRef
        (frozenRefCompileCtx compileEnv
          (preseedContextBlockEnv blockEnv input.2) snapshot)
        input.1 = some target) :
    MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport source := by
  cases hbound with
  | @defn definitionData htypeBound hvalueBound =>
      have htypeMem :
          (definitionData.type, definitionData.levelParams.toList) ∈
            Ix.CompileM.mutConstPreseedInputs (.defn definitionData) := by
        simp [Ix.CompileM.mutConstPreseedInputs]
      have hvalueMem :
          (definitionData.value, definitionData.levelParams.toList) ∈
            Ix.CompileM.mutConstPreseedInputs (.defn definitionData) := by
        simp [Ix.CompileM.mutConstPreseedInputs]
      obtain ⟨typeTarget, htypeRef⟩ := htargets _ htypeMem
      obtain ⟨valueTarget, hvalueRef⟩ := htargets _ hvalueMem
      apply MutConstOrdinaryReady.defn
      refine {
        typeSource := hsources _ htypeMem
        valueSource := hsources _ hvalueMem
        typeBound := htypeBound
        valueBound := hvalueBound
        typeRef := ⟨typeTarget, ?_⟩
        valueRef := ⟨valueTarget, ?_⟩ }
      · simpa [definitionDataCompileBlockEnv,
          preseedContextBlockEnv, frozenRefCompileCtx] using htypeRef
      · simpa [definitionDataCompileBlockEnv,
          preseedContextBlockEnv, frozenRefCompileCtx] using hvalueRef
  | @indc inductiveData htypeBound hctorBounds hctorCount hctorParams =>
      have htypeMem :
          (inductiveData.type, inductiveData.levelParams.toList) ∈
            Ix.CompileM.mutConstPreseedInputs (.indc inductiveData) := by
        simp [Ix.CompileM.mutConstPreseedInputs]
      obtain ⟨typeTarget, htypeRef⟩ := htargets _ htypeMem
      apply MutConstOrdinaryReady.indc
      refine {
        typeSource := hsources _ htypeMem
        ctorSources := ?_
        typeBound := htypeBound
        ctorBounds := hctorBounds
        ctorCount := hctorCount
        typeRef := ⟨typeTarget, ?_⟩
        ctorRefs := ?_ }
      · intro ctor hmem
        have hctorMem :
            (ctor.cnst.type, ctor.cnst.levelParams.toList) ∈
              Ix.CompileM.mutConstPreseedInputs (.indc inductiveData) := by
          simp only [Ix.CompileM.mutConstPreseedInputs, List.mem_cons]
          exact Or.inr (List.mem_map.mpr ⟨ctor, hmem, rfl⟩)
        exact hsources _ hctorMem
      · simpa [inductiveDataCompileBlockEnv,
          preseedContextBlockEnv, frozenRefCompileCtx] using htypeRef
      · intro ctor hmem
        have hctorMem :
            (ctor.cnst.type, ctor.cnst.levelParams.toList) ∈
              Ix.CompileM.mutConstPreseedInputs (.indc inductiveData) := by
          simp only [Ix.CompileM.mutConstPreseedInputs, List.mem_cons]
          exact Or.inr (List.mem_map.mpr ⟨ctor, hmem, rfl⟩)
        obtain ⟨target, href⟩ := htargets _ hctorMem
        refine ⟨target, ?_⟩
        simpa [inductiveDataCompileBlockEnv, preseedContextBlockEnv,
          frozenRefCompileCtx, hctorParams ctor hmem] using href
  | @recr recursorVal htypeBound hruleBounds hruleCount =>
      have htypeMem :
          (recursorVal.cnst.type, recursorVal.cnst.levelParams.toList) ∈
            Ix.CompileM.mutConstPreseedInputs (.recr recursorVal) := by
        simp [Ix.CompileM.mutConstPreseedInputs,
          Ix.CompileM.recursorSourceExprs]
      obtain ⟨typeTarget, htypeRef⟩ := htargets _ htypeMem
      apply MutConstOrdinaryReady.recr
      refine {
        typeSource := hsources _ htypeMem
        ruleSources := ?_
        typeBound := htypeBound
        ruleBounds := hruleBounds
        ruleCount := hruleCount
        typeRef := ⟨typeTarget, ?_⟩
        ruleRefs := ?_ }
      · intro rule hmem
        have hruleMem :
            (rule.rhs, recursorVal.cnst.levelParams.toList) ∈
              Ix.CompileM.mutConstPreseedInputs (.recr recursorVal) := by
          simp only [Ix.CompileM.mutConstPreseedInputs]
          apply List.mem_map.mpr
          exact ⟨rule.rhs, List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨rule, hmem, rfl⟩), rfl⟩
        exact hsources _ hruleMem
      · simpa [recursorCompileBlockEnv, preseedContextBlockEnv,
          frozenRefCompileCtx] using htypeRef
      · intro rule hmem
        have hruleMem :
            (rule.rhs, recursorVal.cnst.levelParams.toList) ∈
              Ix.CompileM.mutConstPreseedInputs (.recr recursorVal) := by
          simp only [Ix.CompileM.mutConstPreseedInputs]
          apply List.mem_map.mpr
          exact ⟨rule.rhs, List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨rule, hmem, rfl⟩), rfl⟩
        obtain ⟨target, href⟩ := htargets _ hruleMem
        refine ⟨target, ?_⟩
        simpa [recursorCompileBlockEnv, preseedContextBlockEnv,
          frozenRefCompileCtx] using href

/-- The concrete ordinary member compilers discharge the abstract fold
contract from one shared frozen preseed snapshot. -/
theorem mutConstMemberRunWireReady_of_ordinary
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    {source : Ix.MutConst}
    (hready : MutConstOrdinaryReady compileEnv blockEnv snapshot
      levelSupport source) :
    MutConstMemberRunWireReady compileEnv blockEnv
      (MutualMemberStateWF snapshot) source := by
  intro state hstate
  cases hready with
  | @defn definitionData hdefinition =>
    obtain ⟨typeTarget, htypeRef⟩ := hdefinition.typeRef
    obtain ⟨valueTarget, hvalueRef⟩ := hdefinition.valueRef
    have hstart : FrozenExprStateWF compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData)
        levelSupport snapshot (definitionCompileStartState state) :=
      hstate.definitionCompileStartState_frozen compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
    obtain ⟨constMeta, state', hrun, htables', htableEq, hwire,
        hexprCache, hcanonCache⟩ :=
      compileDefinitionData_run_ordinary_wireWF compileEnv blockEnv snapshot
        hfree hclosed hlevelFaithful hexprFaithful htables definitionData
        hdefinition.typeSource hdefinition.valueSource hdefinition.typeBound
        hdefinition.valueBound hstart htypeRef hvalueRef
    let payload := compiledDefinitionDataPayload definitionData typeTarget
      valueTarget
    let member : Ix.CompileM.CompiledMutConstMember := {
      payload := .defn payload
      roots := #[typeTarget, valueTarget]
      metas := #[(definitionData.name, constMeta)] }
    have hroots : ExprArrayWireWF member.roots := by
      intro expr hmem
      have heq : expr = typeTarget ∨ expr = valueTarget := by
        simpa [member] using hmem
      rcases heq with rfl | rfl
      · exact hwire.1
      · exact hwire.2
    refine ⟨member, state', ?_, ⟨htableEq, hexprCache, hcanonCache⟩,
      ⟨?_, hroots⟩⟩
    · have hwith : Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withCurrent definitionData.name
            (Ix.CompileM.compileDefinitionData definitionData)) =
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionData definitionData) := by
        rfl
      unfold Ix.CompileM.compileMutConstMember
      rw [run_bind, hwith, hrun]
      rfl
    · exact hwire
  | @indc inductiveData hinductive =>
    have hstart : FrozenExprStateWF compileEnv
        (inductiveDataCompileBlockEnv blockEnv inductiveData)
        levelSupport snapshot (axiomCompileStartState state) :=
      hstate.axiomCompileStartState_frozen compileEnv
        (inductiveDataCompileBlockEnv blockEnv inductiveData) levelSupport
    obtain ⟨ind, indMeta, ctorMetaPairs, roots, state', hrun, htables',
        htableEq, hwire, hroots, hexprCache, hcanonCache⟩ :=
      compileInductiveData_run_ordinary_wireWF compileEnv blockEnv snapshot
        hfree hclosed hlevelFaithful hexprFaithful htables inductiveData
        hinductive.typeSource hinductive.ctorSources hinductive.typeBound
        hinductive.ctorBounds hinductive.ctorCount hstart
        hinductive.typeRef hinductive.ctorRefs
    let member : Ix.CompileM.CompiledMutConstMember := {
      payload := .indc ind
      roots := roots
      metas := #[(inductiveData.name, indMeta)] ++ ctorMetaPairs }
    refine ⟨member, state', ?_, ⟨htableEq, hexprCache, hcanonCache⟩,
      ⟨hwire, hroots⟩⟩
    have hwith : Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withCurrent inductiveData.name
            (Ix.CompileM.compileInductiveData inductiveData)) =
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveData inductiveData) := by
      rfl
    unfold Ix.CompileM.compileMutConstMember
    rw [run_bind, hwith, hrun]
    rfl
  | @recr recursorVal hrecursor =>
    have hstart : FrozenExprStateWF compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal)
        levelSupport snapshot (axiomCompileStartState state) :=
      hstate.axiomCompileStartState_frozen compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) levelSupport
    obtain ⟨recursor, constMeta, state', hrun, htables', htableEq,
        hwire, hexprCache, hcanonCache⟩ :=
      compileRecursor_run_ordinary_wireWF compileEnv blockEnv snapshot
        hfree hclosed hlevelFaithful hexprFaithful htables recursorVal
        hrecursor.typeSource hrecursor.ruleSources hrecursor.typeBound
        hrecursor.ruleBounds hrecursor.ruleCount hstart hrecursor.typeRef
        hrecursor.ruleRefs
    let member : Ix.CompileM.CompiledMutConstMember := {
      payload := .recr recursor
      roots := #[recursor.typ] ++ recursor.rules.map (·.rhs)
      metas := #[(recursorVal.cnst.name, constMeta)] }
    have htypeRoots : ExprArrayWireWF #[recursor.typ] := by
      intro expr hmem
      have heq : expr = recursor.typ := by simpa using hmem
      subst expr
      exact hwire.1
    have hruleRoots : ExprArrayWireWF (recursor.rules.map (·.rhs)) := by
      intro expr hmem
      obtain ⟨rule, hrule, rfl⟩ := Array.mem_map.mp hmem
      exact hwire.2.2 rule hrule
    have hroots : ExprArrayWireWF member.roots :=
      exprArrayWireWF_append htypeRoots hruleRoots
    refine ⟨member, state', ?_, ⟨htableEq, hexprCache, hcanonCache⟩,
      ⟨hwire, hroots⟩⟩
    have hwith : Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withCurrent recursorVal.cnst.name
            (Ix.CompileM.compileRecursorData recursorVal)) =
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursor recursorVal) := by
      rfl
    unfold Ix.CompileM.compileMutConstMember
    rw [run_bind, hwith, hrun]
    rfl

/-- Number of nonempty equivalence classes, hence the exact number of
representative payloads appended by the class fold. -/
def nonemptyMutConstClassCount : List (List Ix.MutConst) → Nat
  | [] => 0
  | [] :: rest => nonemptyMutConstClassCount rest
  | (_ :: _) :: rest => nonemptyMutConstClassCount rest + 1

/-- Equivalent members preserve payload/root wire safety and never change the
representative count. -/
theorem compileEquivalentMutConsts_run_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (StateInv : Ix.CompileM.BlockState → Prop)
    (sources : List Ix.MutConst)
    (hmembers : ∀ source ∈ sources,
      MutConstMemberRunWireReady compileEnv blockEnv StateInv source)
    (acc : Ix.CompileM.MutConstCompileState)
    (hacc : MutConstCompileStateWireWF acc)
    (state : Ix.CompileM.BlockState) (hstate : StateInv state) :
    ∃ finalAcc finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileEquivalentMutConsts sources acc) =
        .ok (finalAcc, finalState) ∧
      StateInv finalState ∧
      MutConstCompileStateWireWF finalAcc ∧
      finalAcc.payloads.size = acc.payloads.size ∧
      finalAcc.roots = acc.roots := by
  induction sources generalizing acc state with
  | nil =>
      exact ⟨acc, state, rfl, hstate, hacc, rfl, rfl⟩
  | cons source rest ih =>
      obtain ⟨member, memberState, hmemberRun, hmemberState,
          hmemberWire⟩ := hmembers source (by simp) state hstate
      let nextAcc := acc.addEquivalent member
      have hnextAcc : MutConstCompileStateWireWF nextAcc :=
        hacc.addEquivalent member
      have hrest : ∀ item ∈ rest,
          MutConstMemberRunWireReady compileEnv blockEnv StateInv item := by
        intro item hmem
        exact hmembers item (by simp [hmem])
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalAcc,
          hsize, hroots⟩ :=
        ih hrest nextAcc hnextAcc memberState hmemberState
      refine ⟨finalAcc, finalState, ?_, hfinalState, hfinalAcc, ?_, ?_⟩
      · unfold Ix.CompileM.compileEquivalentMutConsts
        rw [run_bind, hmemberRun]
        exact hrestRun
      · exact hsize
      · exact hroots

/-- One nonempty class appends exactly one wire-safe representative; an empty
class is the identity. -/
theorem compileMutConstClass_run_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (StateInv : Ix.CompileM.BlockState → Prop)
    (sources : List Ix.MutConst)
    (hmembers : ∀ source ∈ sources,
      MutConstMemberRunWireReady compileEnv blockEnv StateInv source)
    (acc : Ix.CompileM.MutConstCompileState)
    (hacc : MutConstCompileStateWireWF acc)
    (state : Ix.CompileM.BlockState) (hstate : StateInv state) :
    ∃ finalAcc finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConstClass sources acc) =
        .ok (finalAcc, finalState) ∧
      StateInv finalState ∧
      MutConstCompileStateWireWF finalAcc ∧
      finalAcc.payloads.size = acc.payloads.size +
        (if sources.isEmpty then 0 else 1) := by
  cases sources with
  | nil =>
      exact ⟨acc, state, rfl, hstate, hacc, by simp⟩
  | cons representative equivalents =>
      obtain ⟨member, memberState, hmemberRun, hmemberState,
          hmemberWire⟩ := hmembers representative (by simp) state hstate
      let nextAcc := acc.addRepresentative member
      have hnextAcc : MutConstCompileStateWireWF nextAcc :=
        hacc.addRepresentative hmemberWire
      have hequivalents : ∀ source ∈ equivalents,
          MutConstMemberRunWireReady compileEnv blockEnv StateInv source := by
        intro source hmem
        exact hmembers source (by simp [hmem])
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalAcc,
          hsize, hroots⟩ :=
        compileEquivalentMutConsts_run_wireWF compileEnv blockEnv StateInv
          equivalents hequivalents nextAcc hnextAcc memberState hmemberState
      refine ⟨finalAcc, finalState, ?_, hfinalState, hfinalAcc, ?_⟩
      · unfold Ix.CompileM.compileMutConstClass
        rw [run_bind, hmemberRun]
        exact hrestRun
      · simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        rw [hsize]
        simp [nextAcc, Ix.CompileM.MutConstCompileState.addRepresentative]

/-- The outer class fold preserves the live invariant and appends exactly one
payload for every nonempty class. -/
theorem compileMutConstClasses_run_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (StateInv : Ix.CompileM.BlockState → Prop)
    (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstMemberRunWireReady compileEnv blockEnv StateInv source)
    (acc : Ix.CompileM.MutConstCompileState)
    (hacc : MutConstCompileStateWireWF acc)
    (state : Ix.CompileM.BlockState) (hstate : StateInv state) :
    ∃ finalAcc finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConstClasses classes acc) =
        .ok (finalAcc, finalState) ∧
      StateInv finalState ∧
      MutConstCompileStateWireWF finalAcc ∧
      finalAcc.payloads.size =
        acc.payloads.size + nonemptyMutConstClassCount classes := by
  induction classes generalizing acc state with
  | nil =>
      exact ⟨acc, state, rfl, hstate, hacc, by simp [nonemptyMutConstClassCount]⟩
  | cons constClass rest ih =>
      have hclassMembers : ∀ source ∈ constClass,
          MutConstMemberRunWireReady compileEnv blockEnv StateInv source := by
        intro source hmem
        exact hmembers constClass (by simp) source hmem
      obtain ⟨classAcc, classState, hclassRun, hclassState, hclassAcc,
          hclassSize⟩ :=
        compileMutConstClass_run_wireWF compileEnv blockEnv StateInv
          constClass hclassMembers acc hacc state hstate
      have hrestMembers : ∀ cls ∈ rest, ∀ source ∈ cls,
          MutConstMemberRunWireReady compileEnv blockEnv StateInv source := by
        intro cls hcls source hsource
        exact hmembers cls (by simp [hcls]) source hsource
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalAcc,
          hfinalSize⟩ :=
        ih hrestMembers classAcc hclassAcc classState hclassState
      refine ⟨finalAcc, finalState, ?_, hfinalState, hfinalAcc, ?_⟩
      · unfold Ix.CompileM.compileMutConstClasses
        rw [run_bind, hclassRun]
        exact hrestRun
      · rw [hfinalSize, hclassSize]
        cases constClass with
        | nil => simp [nonemptyMutConstClassCount]
        | cons representative equivalents =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hclassSize
          simp [nonemptyMutConstClassCount, Nat.add_assoc, Nat.add_comm]

/-- The public member-fold wrapper returns exactly the representative array,
root array, and metadata array proved by the recursive class fold. -/
theorem compileMutConsts_run_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (StateInv : Ix.CompileM.BlockState → Prop)
    (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstMemberRunWireReady compileEnv blockEnv StateInv source)
    (state : Ix.CompileM.BlockState) (hstate : StateInv state) :
    ∃ payloads roots metas finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConsts classes) =
        .ok ((payloads, roots, metas), finalState) ∧
      StateInv finalState ∧
      (∀ payload ∈ payloads, payload.wireWF) ∧
      ExprArrayWireWF roots ∧
      payloads.size = nonemptyMutConstClassCount classes := by
  obtain ⟨finalAcc, finalState, hrun, hfinalState, hfinalWire, hsize⟩ :=
    compileMutConstClasses_run_wireWF compileEnv blockEnv StateInv classes
      hmembers {} MutConstCompileStateWireWF.empty state hstate
  refine ⟨finalAcc.payloads, finalAcc.roots, finalAcc.metas, finalState,
    ?_, hfinalState, hfinalWire.payloads, hfinalWire.roots, ?_⟩
  · unfold Ix.CompileM.compileMutConsts
    rw [run_bind, hrun]
    rfl
  · simpa using hsize

/-- Concrete ordinary compilation of every member in every class satisfies
the public member-fold contract and preserves the frozen inter-member state. -/
theorem compileMutConsts_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport source)
    (state : Ix.CompileM.BlockState)
    (hstate : MutualMemberStateWF snapshot state) :
    ∃ payloads roots metas finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConsts classes) =
        .ok ((payloads, roots, metas), finalState) ∧
      MutualMemberStateWF snapshot finalState ∧
      (∀ payload ∈ payloads, payload.wireWF) ∧
      ExprArrayWireWF roots ∧
      payloads.size = nonemptyMutConstClassCount classes := by
  apply compileMutConsts_run_wireWF compileEnv blockEnv
    (MutualMemberStateWF snapshot) classes
  · intro constClass hclass source hsource
    exact mutConstMemberRunWireReady_of_ordinary compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables
      (hmembers constClass hclass source hsource)
  · exact hstate

/-- Adding the structural representative-count bound turns the compiled
payload array into a wire-safe mutual `ConstantInfo`. -/
theorem compileMutConsts_run_ordinary_mutualInfoWireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size)
    (state : Ix.CompileM.BlockState)
    (hstate : MutualMemberStateWF snapshot state) :
    ∃ payloads roots metas finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutConsts classes) =
        .ok ((payloads, roots, metas), finalState) ∧
      MutualMemberStateWF snapshot finalState ∧
      (Ixon.ConstantInfo.muts payloads).wireWF ∧
      ExprArrayWireWF roots := by
  obtain ⟨payloads, roots, metas, finalState, hrun, hfinalState,
      hpayloads, hroots, hsize⟩ :=
    compileMutConsts_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables classes hmembers state
      hstate
  have hpayloadCount : payloads.size < UInt64.size := by
    rw [hsize]
    exact hcount
  exact ⟨payloads, roots, metas, finalState, hrun, hfinalState,
    ⟨hpayloadCount, hpayloads⟩, hroots⟩

/-! ## Compiled block assembly -/

theorem standaloneMutConstInfo?_wireWF
    (payloads : Array Ixon.MutConst)
    (hpayloads : ∀ payload ∈ payloads, payload.wireWF)
    {info : Ixon.ConstantInfo}
    (hinfo : Ix.CompileM.standaloneMutConstInfo? payloads = some info) :
    info.wireWF := by
  unfold Ix.CompileM.standaloneMutConstInfo? at hinfo
  split at hinfo
  next hsize =>
    have hsize' : payloads.size = 1 := by simpa using hsize
    have hzero : 0 < payloads.size := by omega
    have hmem : payloads[0]! ∈ payloads := by
      rw [getElem!_pos payloads 0 hzero]
      exact Array.getElem_mem hzero
    have hpayload := hpayloads payloads[0]! hmem
    cases hfirst : payloads[0]! with
    | defn definition =>
        simp only [hfirst] at hinfo hpayload
        cases hinfo
        exact hpayload
    | recr recursor =>
        simp only [hfirst] at hinfo hpayload
        cases hinfo
        exact hpayload
    | indc inductiveInfo =>
        simp only [hfirst] at hinfo
        cases hinfo
  next hsize =>
    simp at hinfo

/-- Both the standalone-collapse and general mutual-wrapper branches produce
an exactly decodable main block. Projection construction is deliberately
irrelevant to this codec postcondition. -/
theorem buildCompiledMutualBlock_codecWF
    (classes : List (List Ix.MutConst))
    (payloads : Array Ixon.MutConst) (roots : Array Ixon.Expr)
    (metas : Array (Ix.Name × Ixon.ConstantMeta))
    (cache : Ix.CompileM.BlockState)
    (hpayloadCount : payloads.size < UInt64.size)
    (hpayloads : ∀ payload ∈ payloads, payload.wireWF)
    (hroots : ExprArrayWireWF roots)
    (htables : BlockWireTablesWF cache) :
    BlockResultCodecWF
      (Ix.CompileM.buildCompiledMutualBlock classes payloads roots metas
        cache) := by
  generalize hstandalone :
    Ix.CompileM.standaloneMutConstInfo? payloads = standalone
  cases standalone with
  | none =>
      let info : Ixon.ConstantInfo := .muts payloads
      have hinfo : info.wireWF := ⟨hpayloadCount, hpayloads⟩
      let block := Ix.CompileM.buildConstantWithSharing info roots
        cache.refs cache.univs
      have hblock : block.wireWF :=
        buildConstantWithSharing_wireWF info roots hinfo hroots htables
      simpa [Ix.CompileM.buildCompiledMutualBlock, hstandalone, info,
        block] using
        (BlockResult.mk'_codecWF block .empty
          (Ix.CompileM.buildMutualProjections classes
            (Address.blake3 (Ixon.ser block)) metas) hblock)
  | some info =>
      have hinfo : info.wireWF :=
        standaloneMutConstInfo?_wireWF payloads hpayloads hstandalone
      let block := Ix.CompileM.buildConstantWithSharing info roots
        cache.refs cache.univs
      have hblock : block.wireWF :=
        buildConstantWithSharing_wireWF info roots hinfo hroots htables
      simpa [Ix.CompileM.buildCompiledMutualBlock, hstandalone, block] using
        (BlockResult.mk'_codecWF block .empty
          (Ix.CompileM.buildStandaloneMutualProjections classes block metas)
          hblock)

/-- The state-reading finalizer is total, leaves the compiler state unchanged,
and inherits the pure assembler's codec postcondition. -/
theorem finishMutualCompilation_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    (classes : List (List Ix.MutConst))
    (payloads : Array Ixon.MutConst) (roots : Array Ixon.Expr)
    (metas : Array (Ix.Name × Ixon.ConstantMeta))
    (hpayloadCount : payloads.size < UInt64.size)
    (hpayloads : ∀ payload ∈ payloads, payload.wireWF)
    (hroots : ExprArrayWireWF roots)
    (htables : BlockWireTablesWF state) :
    ∃ result,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishMutualCompilation classes payloads roots metas) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  let result := Ix.CompileM.buildCompiledMutualBlock classes payloads roots
    metas state
  refine ⟨result, rfl, ?_⟩
  exact buildCompiledMutualBlock_codecWF classes payloads roots metas state
    hpayloadCount hpayloads hroots htables

/-- The complete post-preseed mutual payload phase compiles all class members,
retains one representative per nonempty class, and returns a codec-safe main
block through either assembler branch. -/
theorem compileMutualPayload_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (classes : List (List Ix.MutConst))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryReady compileEnv blockEnv snapshot levelSupport source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size)
    (state : Ix.CompileM.BlockState)
    (hstate : MutualMemberStateWF snapshot state) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualPayload classes) =
        .ok (result, finalState) ∧
      MutualMemberStateWF snapshot finalState ∧
      BlockResultCodecWF result := by
  obtain ⟨payloads, roots, metas, compiledState, hcompile,
      hcompiledState, hpayloads, hroots, hsize⟩ :=
    compileMutConsts_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables classes hmembers state
      hstate
  have hpayloadCount : payloads.size < UInt64.size := by
    rw [hsize]
    exact hcount
  have hcompiledTables : BlockWireTablesWF compiledState :=
    htables.of_exprTableView_eq hcompiledState.tables
  obtain ⟨result, hfinish, hcodec⟩ :=
    finishMutualCompilation_run_codecWF compileEnv blockEnv compiledState
      classes payloads roots metas hpayloadCount hpayloads hroots
      hcompiledTables
  refine ⟨result, compiledState, ?_, hcompiledState, hcodec⟩
  unfold Ix.CompileM.compileMutualPayload
  rw [run_bind, hcompile]
  exact hfinish

/-! ## Full mutual driver above the heterogeneous preseed boundary -/

theorem auditMutualConstructorPlanHeads_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (constructors : List Ix.ConstructorVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditMutualConstructorPlanHeads constructors) =
      .ok ((), state) := by
  induction constructors with
  | nil => rfl
  | cons ctor rest ih =>
      unfold Ix.CompileM.auditMutualConstructorPlanHeads
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
          ctor.cnst.name ctor.cnst.type hfree]
      exact ih

theorem auditMutConstPlanHeads_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.MutConst)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditMutConstPlanHeads source) = .ok ((), state) := by
  cases source with
  | defn definitionData =>
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        Ix.CompileM.auditPlanHeadArities definitionData.name
          definitionData.type
        Ix.CompileM.auditPlanHeadArities definitionData.name
          definitionData.value) = .ok ((), state)
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
          definitionData.name definitionData.type hfree]
      exact auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
        definitionData.name definitionData.value hfree
  | indc inductiveData =>
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        Ix.CompileM.auditPlanHeadArities inductiveData.name inductiveData.type
        Ix.CompileM.auditMutualConstructorPlanHeads
          inductiveData.ctors.toList) = .ok ((), state)
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
          inductiveData.name inductiveData.type hfree]
      exact auditMutualConstructorPlanHeads_run_surgeryFree compileEnv
        blockEnv state inductiveData.ctors.toList hfree
  | recr recursorVal =>
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        Ix.CompileM.auditPlanHeadArities recursorVal.cnst.name
          recursorVal.cnst.type
        Ix.CompileM.auditRecursorRulePlanHeads recursorVal.cnst.name
          recursorVal.rules.toList) = .ok ((), state)
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
          recursorVal.cnst.name recursorVal.cnst.type hfree]
      exact auditRecursorRulePlanHeads_run_surgeryFree compileEnv blockEnv
        state recursorVal.cnst.name recursorVal.rules.toList hfree

theorem auditMutConstClassPlanHeads_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (sources : List Ix.MutConst)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditMutConstClassPlanHeads sources) =
      .ok ((), state) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      unfold Ix.CompileM.auditMutConstClassPlanHeads
      rw [run_bind,
        auditMutConstPlanHeads_run_surgeryFree compileEnv blockEnv state
          source hfree]
      exact ih

theorem auditMutConstClassesPlanHeads_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (classes : List (List Ix.MutConst))
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditMutConstClassesPlanHeads classes) =
      .ok ((), state) := by
  induction classes with
  | nil => rfl
  | cons constClass rest ih =>
      unfold Ix.CompileM.auditMutConstClassesPlanHeads
      rw [run_bind,
        auditMutConstClassPlanHeads_run_surgeryFree compileEnv blockEnv state
          constClass hfree]
      exact ih

def mutualCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (classes : List (List Ix.MutConst)) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx := Ix.MutConst.ctx classes }

/-- Once heterogeneous preseeding has produced its frozen snapshot, the exact
production mutual driver—including audit, mutual-context installation, every
class member, standalone collapse, projections, sharing, and serialization—
returns a codec-safe main block. -/
theorem compileMutualBlock_run_of_preseed_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state snapshot : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (classes : List (List Ix.MutConst))
    (hpreseed : Ix.CompileM.CompileM.run compileEnv
      (mutualCompileBlockEnv blockEnv classes) state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.mutualPreseedExprs classes)) = .ok ((), snapshot))
    (htables : BlockWireTablesWF snapshot)
    (hexprCache : snapshot.exprCache = {})
    (hcanonCache : CanonUnivCacheWF snapshot)
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryReady compileEnv
        (mutualCompileBlockEnv blockEnv classes) snapshot levelSupport source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualBlock classes) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  have hstart : MutualMemberStateWF snapshot snapshot :=
    ⟨rfl, hexprCache, hcanonCache⟩
  obtain ⟨result, finalState, hpayload, hfinalState, hcodec⟩ :=
    compileMutualPayload_run_ordinary_codecWF compileEnv
      (mutualCompileBlockEnv blockEnv classes) snapshot hfree hclosed
      hlevelFaithful hexprFaithful htables classes hmembers hcount snapshot
      hstart
  refine ⟨result, finalState, ?_, hcodec⟩
  unfold Ix.CompileM.compileMutualBlock
  rw [run_bind,
    auditMutConstClassesPlanHeads_run_surgeryFree compileEnv blockEnv state
      classes hfree]
  simp only
  rw [run_withMutCtx]
  change Ix.CompileM.CompileM.run compileEnv
    (mutualCompileBlockEnv blockEnv classes) state (do
      Ix.CompileM.preseedExprTables (Ix.CompileM.mutualPreseedExprs classes)
      Ix.CompileM.compileMutualPayload classes) = _
  rw [run_bind, hpreseed]
  exact hpayload

/-- Source readiness now constructs the heterogeneous production preseed and
closes the full mutual driver without a raw execution hypothesis. The shared
seen-set safety predicate records the explicit digest/context collision
boundary; all remaining premises are structural source, count, and table
capacity conditions. -/
theorem compileMutualBlock_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (classes : List (List Ix.MutConst))
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hready : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (mutualCompileBlockEnv blockEnv classes) input.2)
        levelSupport (preseedContextStartState state) input.1)
    (hseen : HeterogeneousPreseedSeenSafe compileEnv
      (mutualCompileBlockEnv blockEnv classes)
      (preseedContextStartState state)
      (Ix.CompileM.mutualPreseedInputs classes) (#[], #[], {}) state)
    (htableBound : InputPreseedSourceBound
      (mutualCompileBlockEnv blockEnv classes) state
      (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualBlock classes) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  let mutualEnv := mutualCompileBlockEnv blockEnv classes
  let inputs := Ix.CompileM.mutualPreseedInputs classes
  obtain ⟨snapshot, hpreseed, htables, htargets, hsnapshotExpr,
      hsnapshotCanon, hsnapshotArena, hsnapshotFinal⟩ :=
    preseedExprTables_inputs_run_ready_frozenRefs compileEnv mutualEnv state
      hclosed hlevelFaithful hexprFaithful inputs hready hseen hcanonCache
      hrefTable hunivTable htableBound
  have hpreseed' : Ix.CompileM.CompileM.run compileEnv mutualEnv state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.mutualPreseedExprs classes)) =
        .ok ((), snapshot) := by
    simpa [inputs, Ix.CompileM.mutualPreseedExprs] using hpreseed
  have hsnapshotExpr' : snapshot.exprCache = {} :=
    hsnapshotExpr.trans hexprCache
  have hmemberReady : ∀ constClass ∈ classes,
      ∀ source ∈ constClass,
      MutConstOrdinaryReady compileEnv mutualEnv snapshot levelSupport
        source := by
    intro constClass hclass source hsource
    apply MutConstOrdinaryBounds.ready_of_preseed compileEnv mutualEnv snapshot
      (hmembers constClass hclass source hsource)
    · intro input hinput
      exact (hready input
        (mutConstPreseedInputs_mem_mutual hclass hsource hinput)).supported
    · intro input hinput
      exact htargets input
        (mutConstPreseedInputs_mem_mutual hclass hsource hinput)
  exact compileMutualBlock_run_of_preseed_ordinary_codecWF compileEnv
    blockEnv state snapshot hfree hclosed hlevelFaithful hexprFaithful
    classes hpreseed' htables hsnapshotExpr' hsnapshotCanon hmemberReady
    hcount

/-- The full production mutual driver with its shared-seen collision premise
discharged by a uniform universe-parameter context for every preseed root. -/
theorem compileMutualBlock_run_uniform_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (classes : List (List Ix.MutConst)) (params : List Ix.Name)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      input.2 = params)
    (hready : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (mutualCompileBlockEnv blockEnv classes) input.2)
        levelSupport (preseedContextStartState state) input.1)
    (htableBound : InputPreseedSourceBound
      (mutualCompileBlockEnv blockEnv classes) state
      (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualBlock classes) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  have hseen := heterogeneousPreseedSeenSafe_of_uniform compileEnv
    (mutualCompileBlockEnv blockEnv classes) state params hclosed
    hlevelFaithful hexprFaithful
    (Ix.CompileM.mutualPreseedInputs classes) hparams hready hcanonCache
  exact compileMutualBlock_run_ready_codecWF compileEnv blockEnv state hfree
    hclosed hlevelFaithful hexprFaithful classes hexprCache hcanonCache
    hrefTable hunivTable hready hseen htableBound hmembers hcount

/-- Member-local universe-context agreement closes the uniform-context mutual
driver theorem without exposing the flattened production preseed list. -/
theorem compileMutualBlock_run_member_uniform_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (classes : List (List Ix.MutConst)) (params : List Ix.Name)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (huniform : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstUniformPreseedParams params source)
    (hready : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (mutualCompileBlockEnv blockEnv classes) input.2)
        levelSupport (preseedContextStartState state) input.1)
    (htableBound : InputPreseedSourceBound
      (mutualCompileBlockEnv blockEnv classes) state
      (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualBlock classes) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  apply compileMutualBlock_run_uniform_ready_codecWF compileEnv blockEnv
    state hfree hclosed hlevelFaithful hexprFaithful classes params
    hexprCache hcanonCache hrefTable hunivTable
  · exact mutualPreseedInputs_uniform params classes huniform
  · exact hready
  · exact htableBound
  · exact hmembers
  · exact hcount

private theorem run_getCompileEnv_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getCompileEnv = .ok (compileEnv, state) := by
  rfl

private theorem run_getBlockEnv_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getBlockEnv = .ok (blockEnv, state) := by
  rfl

private theorem run_getBlockState_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getBlockState = .ok (state, state) := by
  rfl

private theorem run_restoreBlockState_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state saved : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.modifyBlockState fun _ => saved) = .ok ((), saved) := by
  rfl

private theorem run_lookupConstAddr_resolved_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) (addr : Address)
    (hresolve : resolveConstAddr? compileEnv state name = some addr) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.lookupConstAddr name) = .ok (addr, state) := by
  rw [Ix.CompileM.lookupConstAddr,
    run_bind compileEnv blockEnv state Ix.CompileM.getCompileEnv,
    run_getCompileEnv_entry]
  simp only
  rw [run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState_entry]
  simp only
  unfold resolveConstAddr? at hresolve
  cases hblock : state.blockNameToAddr.get? name with
  | some found =>
      simp only [hblock, Option.some.injEq] at hresolve
      subst found
      simp only
      rfl
  | none =>
      simp only [hblock] at hresolve
      simp only
      cases hglobal : compileEnv.nameToAddr.get? name with
      | some found =>
          simp only [hglobal, Option.some.injEq] at hresolve
          subst found
          simp only
          rfl
      | none =>
          simp only [hglobal] at hresolve
          simp only
          cases hblockAux : state.auxNameToAddr.get? name with
          | some found =>
              simp only [hblockAux, Option.some.injEq] at hresolve
              subst found
              simp only
              rfl
          | none =>
              simp only [hblockAux] at hresolve
              simp only
              change compileEnv.auxNameToAddr.get? name = some addr at hresolve
              rw [hresolve]
              rfl

private theorem sOrderCmpM_run_of_success
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (left right : Ix.CompileM.CompileM SOrder)
    (leftResult rightResult : SOrder)
    (hleft : Ix.CompileM.CompileM.run compileEnv blockEnv state left =
      .ok (leftResult, state))
    (hright : Ix.CompileM.CompileM.run compileEnv blockEnv state right =
      .ok (rightResult, state)) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (SOrder.cmpM left right) = .ok (result, state) := by
  cases leftResult with
  | mk strong ord =>
      cases strong <;> cases ord
      · refine ⟨⟨false, .lt⟩, ?_⟩
        simp [SOrder.cmpM, run_bind, hleft, run_pure]
      · refine ⟨⟨false, rightResult.ord⟩, ?_⟩
        simp only [SOrder.cmpM, run_bind, hleft]
        rw [hright]
        rfl
      · refine ⟨⟨false, .gt⟩, ?_⟩
        simp [SOrder.cmpM, run_bind, hleft, run_pure]
      · refine ⟨⟨true, .lt⟩, ?_⟩
        simp [SOrder.cmpM, run_bind, hleft, run_pure]
      · exact ⟨rightResult, by
          simp [SOrder.cmpM, run_bind, hleft, hright]⟩
      · refine ⟨⟨true, .gt⟩, ?_⟩
        simp [SOrder.cmpM, run_bind, hleft, run_pure]

/-- Exact structural domain on which production universe comparison cannot
reach a metavariable or unknown-parameter error. -/
inductive CompareLevelReady (ctx : List Ix.Name) : Ix.Level → Prop where
  | zero {hash} : CompareLevelReady ctx (.zero hash)
  | succ {level hash} : CompareLevelReady ctx level →
      CompareLevelReady ctx (.succ level hash)
  | max {left right hash} : CompareLevelReady ctx left →
      CompareLevelReady ctx right →
      CompareLevelReady ctx (.max left right hash)
  | imax {left right hash} : CompareLevelReady ctx left →
      CompareLevelReady ctx right →
      CompareLevelReady ctx (.imax left right hash)
  | param {name hash idx} : ctx.idxOf? name = some idx →
      CompareLevelReady ctx (.param name hash)

/-- Acceptance by the total positional reference compiler supplies the exact
structural comparison domain. -/
theorem compareLevelReady_of_ref
    (ctx : List Ix.Name) (level : Ix.Level)
    (href : ∃ target,
      compileUnivRef (univParamIndex ctx) level = some target) :
    CompareLevelReady ctx level := by
  induction level with
  | zero => exact .zero
  | succ level _ ih =>
      simp [compileUnivRef] at href
      rcases href with ⟨_, target, htarget, _⟩
      exact .succ (ih ⟨target, htarget⟩)
  | max left right _ ihleft ihright =>
      simp [compileUnivRef] at href
      rcases href with ⟨_, leftTarget, hleft, rightTarget, hright, _⟩
      exact .max (ihleft ⟨leftTarget, hleft⟩)
        (ihright ⟨rightTarget, hright⟩)
  | imax left right _ ihleft ihright =>
      simp [compileUnivRef] at href
      rcases href with ⟨_, leftTarget, hleft, rightTarget, hright, _⟩
      exact .imax (ihleft ⟨leftTarget, hleft⟩)
        (ihright ⟨rightTarget, hright⟩)
  | param name _ =>
      simp [compileUnivRef, univParamIndex] at href
      rcases href with ⟨_, _, ⟨idx, hidx, _⟩, _⟩
      exact .param hidx
  | mvar => simp [compileUnivRef] at href

/-- Ready universes compare successfully and comparison leaves the block
state unchanged. -/
theorem compareLevel_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (xctx yctx : List Ix.Name) (x y : Ix.Level)
    (hx : CompareLevelReady xctx x)
    (hy : CompareLevelReady yctx y) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compareLevel xctx yctx x y) = .ok (result, state) := by
  induction hx generalizing y with
  | zero =>
      cases hy <;> exact ⟨_, rfl⟩
  | succ _ ih =>
      cases hy with
      | zero | max | imax | param => exact ⟨_, rfl⟩
      | succ hy => exact ih _ hy
  | max _ _ ihl ihr =>
      cases hy with
      | zero | succ | imax | param => exact ⟨_, rfl⟩
      | max hyl hyr =>
          obtain ⟨leftResult, hleft⟩ := ihl _ hyl
          obtain ⟨rightResult, hright⟩ := ihr _ hyr
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            leftResult rightResult hleft hright
  | imax _ _ ihl ihr =>
      cases hy with
      | zero | succ | max | param => exact ⟨_, rfl⟩
      | imax hyl hyr =>
          obtain ⟨leftResult, hleft⟩ := ihl _ hyl
          obtain ⟨rightResult, hright⟩ := ihr _ hyr
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            leftResult rightResult hleft hright
  | param hxi =>
      cases hy with
      | zero | succ | max | imax => exact ⟨_, rfl⟩
      | param hyi =>
          simp only [Ix.CompileM.compareLevel, hxi, hyi]
          exact ⟨_, rfl⟩

/-- Exact source-side domain of expression comparison.  Resolution is
required only for names absent from the current mutual context; comparison
itself never changes the block state. -/
inductive CompareExprReady
    (compileEnv : Ix.CompileM.CompileEnv) (ctx : Ix.MutCtx)
    (levelCtx : List Ix.Name) (origin : Ix.CompileM.BlockState) :
    Ix.Expr → Prop where
  | bvar {idx hash} :
      CompareExprReady compileEnv ctx levelCtx origin (.bvar idx hash)
  | sort {level hash} : CompareLevelReady levelCtx level →
      CompareExprReady compileEnv ctx levelCtx origin (.sort level hash)
  | const {name levels hash} :
      (∀ level ∈ levels.toList, CompareLevelReady levelCtx level) →
      (ctx.get? name = none →
        ∃ addr, resolveConstAddr? compileEnv origin name = some addr) →
      CompareExprReady compileEnv ctx levelCtx origin
        (.const name levels hash)
  | app {fn arg hash} :
      CompareExprReady compileEnv ctx levelCtx origin fn →
      CompareExprReady compileEnv ctx levelCtx origin arg →
      CompareExprReady compileEnv ctx levelCtx origin (.app fn arg hash)
  | lam {name ty body bi hash} :
      CompareExprReady compileEnv ctx levelCtx origin ty →
      CompareExprReady compileEnv ctx levelCtx origin body →
      CompareExprReady compileEnv ctx levelCtx origin
        (.lam name ty body bi hash)
  | all {name ty body bi hash} :
      CompareExprReady compileEnv ctx levelCtx origin ty →
      CompareExprReady compileEnv ctx levelCtx origin body →
      CompareExprReady compileEnv ctx levelCtx origin
        (.forallE name ty body bi hash)
  | letE {name ty value body nonDep hash} :
      CompareExprReady compileEnv ctx levelCtx origin ty →
      CompareExprReady compileEnv ctx levelCtx origin value →
      CompareExprReady compileEnv ctx levelCtx origin body →
      CompareExprReady compileEnv ctx levelCtx origin
        (.letE name ty value body nonDep hash)
  | lit {literal hash} :
      CompareExprReady compileEnv ctx levelCtx origin (.lit literal hash)
  | proj {typeName field value hash} :
      (ctx.get? typeName = none →
        ∃ addr, resolveConstAddr? compileEnv origin typeName = some addr) →
      CompareExprReady compileEnv ctx levelCtx origin value →
      CompareExprReady compileEnv ctx levelCtx origin
        (.proj typeName field value hash)
  | mdata {data inner hash} :
      CompareExprReady compileEnv ctx levelCtx origin inner →
      CompareExprReady compileEnv ctx levelCtx origin
        (.mdata data inner hash)

/-- Preseed readiness contains every fact needed by expression comparison;
wire-size facts are intentionally discarded at this earlier phase. -/
theorem PreseedReady.compareReady
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin : Ix.CompileM.BlockState} {source : Ix.Expr}
    (hready : PreseedReady compileEnv blockEnv levelSupport origin source) :
    CompareExprReady compileEnv blockEnv.mutCtx blockEnv.univCtx origin
      source := by
  induction hready with
  | bvar => exact .bvar
  | sort hlevel href =>
      obtain ⟨target, href, _⟩ := href
      exact .sort (compareLevelReady_of_ref blockEnv.univCtx _
        ⟨target, href⟩)
  | const hlevels hresolve =>
      apply CompareExprReady.const
      · intro level hmem
        obtain ⟨_, target, href, _⟩ := hlevels level (by simpa using hmem)
        exact compareLevelReady_of_ref blockEnv.univCtx level
          ⟨target, href⟩
      · intro hnone
        obtain ⟨addr, haddr, _⟩ := hresolve hnone
        exact ⟨addr, haddr⟩
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihvalue ihbody => exact .letE ihty ihvalue ihbody
  | lit => exact .lit
  | proj hresolve _ ihvalue =>
      apply CompareExprReady.proj
      · intro _
        obtain ⟨addr, haddr, _⟩ := hresolve
        exact ⟨addr, haddr⟩
      · exact ihvalue
  | mdata _ ihinner => exact .mdata ihinner

/-- Comparison readiness is insensitive to state fields outside the frozen
expression-table view (in particular, to comparison-cache inserts). -/
theorem CompareExprReady.of_exprTableView_eq
    {compileEnv : Ix.CompileM.CompileEnv} {ctx : Ix.MutCtx}
    {levelCtx : List Ix.Name} {origin next : Ix.CompileM.BlockState}
    {source : Ix.Expr}
    (hready : CompareExprReady compileEnv ctx levelCtx origin source)
    (hview : exprTableView next = exprTableView origin) :
    CompareExprReady compileEnv ctx levelCtx next source := by
  induction hready with
  | bvar => exact .bvar
  | sort hlevel => exact .sort hlevel
  | const hlevels hresolve =>
      apply CompareExprReady.const hlevels
      intro hnone
      obtain ⟨addr, haddr⟩ := hresolve hnone
      refine ⟨addr, ?_⟩
      rw [resolveConstAddr?_of_exprTableView_eq compileEnv hview]
      exact haddr
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihvalue ihbody => exact .letE ihty ihvalue ihbody
  | lit => exact .lit
  | proj hresolve _ ihvalue =>
      apply CompareExprReady.proj
      · intro hnone
        obtain ⟨addr, haddr⟩ := hresolve hnone
        refine ⟨addr, ?_⟩
        rw [resolveConstAddr?_of_exprTableView_eq compileEnv hview]
        exact haddr
      · exact ihvalue
  | mdata _ ihinner => exact .mdata ihinner

private theorem compareLevelList_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (xctx yctx : List Ix.Name) (xs ys : List Ix.Level)
    (hx : ∀ level ∈ xs, CompareLevelReady xctx level)
    (hy : ∀ level ∈ ys, CompareLevelReady yctx level) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (SOrder.zipM (Ix.CompileM.compareLevel xctx yctx) xs ys) =
        .ok (result, state) := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> exact ⟨_, rfl⟩
  | cons x xs ih =>
      cases ys with
      | nil => exact ⟨_, rfl⟩
      | cons y ys =>
          obtain ⟨headResult, hhead⟩ := compareLevel_run_ready
            compileEnv blockEnv state xctx yctx x y
              (hx x (by simp)) (hy y (by simp))
          have hxs : ∀ level ∈ xs, CompareLevelReady xctx level := by
            intro level hmem
            exact hx level (by simp [hmem])
          have hys : ∀ level ∈ ys, CompareLevelReady yctx level := by
            intro level hmem
            exact hy level (by simp [hmem])
          obtain ⟨tailResult, htail⟩ := ih ys hxs hys
          unfold SOrder.zipM
          rw [run_bind, hhead]
          simp only
          cases headResult with
          | mk strong ord =>
              cases ord
              · exact ⟨_, rfl⟩
              · exact sOrderCmpM_run_of_success compileEnv blockEnv state
                  _ _ ⟨strong, .eq⟩ tailResult rfl htail
              · exact ⟨_, rfl⟩

/-- Ready ordinary expressions compare successfully.  All recursive calls,
including metadata erasure, strictly decrease the source syntax size, and
the comparison phase leaves the entire block state unchanged. -/
theorem compareExpr_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (xlvls ylvls : List Ix.Name) (x y : Ix.Expr)
    (hx : CompareExprReady compileEnv ctx xlvls state x)
    (hy : CompareExprReady compileEnv ctx ylvls state y) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compareExpr ctx xlvls ylvls x y) =
        .ok (result, state) := by
  rw [Ix.CompileM.compareExpr.eq_def]
  cases hx with
  | bvar =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ .bvar hyinner
      | bvar | sort | const | app | lam | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | sort hxlevel =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.sort hxlevel) hyinner
      | sort hylevel =>
          exact compareLevel_run_ready compileEnv blockEnv state
            xlvls ylvls _ _ hxlevel hylevel
      | bvar | const | app | lam | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | @const xname xlevels xhash hxlevels hxresolve =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.const hxlevels hxresolve) hyinner
      | @const yname ylevels yhash hylevels hyresolve =>
          obtain ⟨univs, hunivs⟩ := compareLevelList_run_ready
            compileEnv blockEnv state xlvls ylvls xlevels.toList
              ylevels.toList hxlevels hylevels
          rw [run_bind, hunivs]
          simp only
          by_cases horder : univs.ord != .eq
          · rw [if_pos horder]
            exact ⟨_, rfl⟩
          · rw [if_neg horder]
            by_cases hname : xname == yname
            · rw [if_pos hname]
              exact ⟨_, rfl⟩
            · rw [if_neg hname]
              cases hxctx : ctx.get? xname with
              | some nx =>
                  cases hyctx : ctx.get? yname <;> exact ⟨_, rfl⟩
              | none =>
                  cases hyctx : ctx.get? yname with
                  | some ny => exact ⟨_, rfl⟩
                  | none =>
                      obtain ⟨xaddr, hxaddr⟩ := hxresolve hxctx
                      obtain ⟨yaddr, hyaddr⟩ := hyresolve hyctx
                      rw [run_bind, run_lookupConstAddr_resolved_entry
                        compileEnv blockEnv state xname xaddr hxaddr]
                      simp only
                      rw [run_bind, run_lookupConstAddr_resolved_entry
                        compileEnv blockEnv state yname yaddr hyaddr]
                      exact ⟨_, rfl⟩
      | bvar | sort | app | lam | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | app hxfn hxarg =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.app hxfn hxarg) hyinner
      | app hyfn hyarg =>
          obtain ⟨fnResult, hfn⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxfn hyfn
          obtain ⟨argResult, harg⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxarg hyarg
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            fnResult argResult hfn harg
      | bvar | sort | const | lam | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | lam hxty hxbody =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.lam hxty hxbody) hyinner
      | lam hyty hybody =>
          obtain ⟨tyResult, hty⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxty hyty
          obtain ⟨bodyResult, hbody⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxbody hybody
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            tyResult bodyResult hty hbody
      | bvar | sort | const | app | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | all hxty hxbody =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.all hxty hxbody) hyinner
      | all hyty hybody =>
          obtain ⟨tyResult, hty⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxty hyty
          obtain ⟨bodyResult, hbody⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxbody hybody
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            tyResult bodyResult hty hbody
      | bvar | sort | const | app | lam | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | letE hxty hxvalue hxbody =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.letE hxty hxvalue hxbody) hyinner
      | letE hyty hyvalue hybody =>
          obtain ⟨tyResult, hty⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxty hyty
          obtain ⟨valueResult, hvalue⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxvalue hyvalue
          obtain ⟨bodyResult, hbody⟩ := compareExpr_run_ready compileEnv
            blockEnv state ctx xlvls ylvls _ _ hxbody hybody
          obtain ⟨tailResult, htail⟩ := sOrderCmpM_run_of_success
            compileEnv blockEnv state _ _ valueResult bodyResult
              hvalue hbody
          exact sOrderCmpM_run_of_success compileEnv blockEnv state _ _
            tyResult tailResult hty htail
      | bvar | sort | const | app | lam | all | lit | proj =>
          exact ⟨_, rfl⟩
  | lit =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ .lit hyinner
      | bvar | sort | const | app | lam | all | letE | lit | proj =>
          exact ⟨_, rfl⟩
  | @proj xtypeName xfield xvalue xhash hxresolve hxvalue =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ (.proj hxresolve hxvalue) hyinner
      | @proj ytypeName yfield yvalue yhash hyresolve hyvalue =>
          obtain ⟨valueResult, hvalue⟩ := compareExpr_run_ready
            compileEnv blockEnv state ctx xlvls ylvls _ _ hxvalue hyvalue
          obtain ⟨fieldTail, hfieldTail⟩ := sOrderCmpM_run_of_success
            compileEnv blockEnv state
              (pure (⟨true, compare xfield yfield⟩ : SOrder))
              (Ix.CompileM.compareExpr ctx xlvls ylvls xvalue yvalue)
              ⟨true, compare xfield yfield⟩ valueResult rfl hvalue
          simp only
          let tail := SOrder.cmpM
            (pure (⟨true, compare xfield yfield⟩ : SOrder))
            (Ix.CompileM.compareExpr ctx xlvls ylvls xvalue yvalue)
          have htail (tn : SOrder) : ∃ result,
              Ix.CompileM.CompileM.run compileEnv blockEnv state
                (SOrder.cmpM (pure tn) tail) = .ok (result, state) :=
            sOrderCmpM_run_of_success compileEnv blockEnv state
              (pure tn) tail tn fieldTail rfl (by simpa [tail] using hfieldTail)
          cases hxctx : ctx.get? xtypeName with
          | some nx =>
              cases hyctx : ctx.get? ytypeName with
              | some ny =>
                  exact htail ⟨false, compare nx ny⟩
              | none =>
                  exact htail ⟨true, .lt⟩
          | none =>
              cases hyctx : ctx.get? ytypeName with
              | some ny =>
                  exact htail ⟨true, .gt⟩
              | none =>
                  by_cases hname : xtypeName == ytypeName
                  · rw [if_pos hname]
                    exact htail ⟨true, .eq⟩
                  · rw [if_neg hname]
                    obtain ⟨xaddr, hxaddr⟩ := hxresolve hxctx
                    obtain ⟨yaddr, hyaddr⟩ := hyresolve hyctx
                    rw [run_bind, run_lookupConstAddr_resolved_entry
                      compileEnv blockEnv state xtypeName xaddr hxaddr]
                    simp only
                    rw [run_bind, run_lookupConstAddr_resolved_entry
                      compileEnv blockEnv state ytypeName yaddr hyaddr]
                    exact htail ⟨true, compare xaddr yaddr⟩
      | bvar | sort | const | app | lam | all | letE | lit =>
          exact ⟨_, rfl⟩
  | mdata hxinner =>
      cases hy with
      | mdata hyinner =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner hyinner
      | bvar =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner .bvar
      | sort hylevel =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.sort hylevel)
      | const hylevels hyresolve =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.const hylevels hyresolve)
      | app hyfn hyarg =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.app hyfn hyarg)
      | lam hyty hybody =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.lam hyty hybody)
      | all hyty hybody =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.all hyty hybody)
      | letE hyty hyvalue hybody =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.letE hyty hyvalue hybody)
      | lit =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner .lit
      | proj hyresolve hyvalue =>
          exact compareExpr_run_ready compileEnv blockEnv state ctx
            xlvls ylvls _ _ hxinner (.proj hyresolve hyvalue)
termination_by Ix.CompileM.compareExprSize x +
  Ix.CompileM.compareExprSize y
decreasing_by
  all_goals simp only [Ix.CompileM.compareExprSize_app,
    Ix.CompileM.compareExprSize_lam,
    Ix.CompileM.compareExprSize_forallE,
    Ix.CompileM.compareExprSize_letE,
    Ix.CompileM.compareExprSize_proj,
    Ix.CompileM.compareExprSize_mdata]
  all_goals omega

/-- Member-local source contract for the expressions read by constant
comparison. Constructor types use the parent inductive universe context,
exactly as `compareInd` does. -/
inductive MutConstCompareReady
    (compileEnv : Ix.CompileM.CompileEnv) (ctx : Ix.MutCtx)
    (origin : Ix.CompileM.BlockState) : Ix.MutConst → Prop where
  | defn {definitionData : Ix.Def} :
      CompareExprReady compileEnv ctx definitionData.levelParams.toList
        origin definitionData.type →
      CompareExprReady compileEnv ctx definitionData.levelParams.toList
        origin definitionData.value →
      MutConstCompareReady compileEnv ctx origin (.defn definitionData)
  | indc {inductiveData : Ix.Ind} :
      CompareExprReady compileEnv ctx inductiveData.levelParams.toList
        origin inductiveData.type →
      (∀ ctor ∈ inductiveData.ctors.toList,
        CompareExprReady compileEnv ctx inductiveData.levelParams.toList
          origin ctor.cnst.type) →
      MutConstCompareReady compileEnv ctx origin (.indc inductiveData)
  | recr {recursorVal : Ix.RecursorVal} :
      CompareExprReady compileEnv ctx recursorVal.cnst.levelParams.toList
        origin recursorVal.cnst.type →
      (∀ rule ∈ recursorVal.rules.toList,
        CompareExprReady compileEnv ctx recursorVal.cnst.levelParams.toList
          origin rule.rhs) →
      MutConstCompareReady compileEnv ctx origin (.recr recursorVal)

private theorem run_modifyBlockState_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (f : Ix.CompileM.BlockState → Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.modifyBlockState f) = .ok ((), f state) := by
  rfl

private theorem compareDef_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state : Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (x y : Ix.Def)
    (hxtype : CompareExprReady compileEnv ctx x.levelParams.toList
      origin x.type)
    (hxvalue : CompareExprReady compileEnv ctx x.levelParams.toList
      origin x.value)
    (hytype : CompareExprReady compileEnv ctx y.levelParams.toList
      origin y.type)
    (hyvalue : CompareExprReady compileEnv ctx y.levelParams.toList
      origin y.value)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compareDef ctx x y) = .ok (result, state) := by
  obtain ⟨typeResult, htype⟩ := compareExpr_run_ready compileEnv blockEnv
    state ctx x.levelParams.toList y.levelParams.toList x.type y.type
    (hxtype.of_exprTableView_eq hview) (hytype.of_exprTableView_eq hview)
  obtain ⟨valueResult, hvalue⟩ := compareExpr_run_ready compileEnv
    blockEnv state ctx x.levelParams.toList y.levelParams.toList x.value
    y.value (hxvalue.of_exprTableView_eq hview)
      (hyvalue.of_exprTableView_eq hview)
  obtain ⟨exprResult, hexprs⟩ := sOrderCmpM_run_of_success compileEnv
    blockEnv state _ _ typeResult valueResult htype hvalue
  obtain ⟨levelResult, hlevels⟩ := sOrderCmpM_run_of_success compileEnv
    blockEnv state (pure ⟨true,
      compare x.levelParams.size y.levelParams.size⟩) _ _ exprResult
      rfl hexprs
  obtain ⟨result, hresult⟩ := sOrderCmpM_run_of_success compileEnv
    blockEnv state (pure ⟨true, compare x.kind y.kind⟩) _ _ levelResult
      rfl hlevels
  exact ⟨result, by simpa [Ix.CompileM.compareDef] using hresult⟩

private theorem compareRule_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state : Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (xlvls ylvls : List Ix.Name)
    (x y : Ix.RecursorRule)
    (hx : CompareExprReady compileEnv ctx xlvls origin x.rhs)
    (hy : CompareExprReady compileEnv ctx ylvls origin y.rhs)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compareRule ctx xlvls ylvls x y) =
        .ok (result, state) := by
  obtain ⟨rhsResult, hrhs⟩ := compareExpr_run_ready compileEnv blockEnv
    state ctx xlvls ylvls x.rhs y.rhs
      (hx.of_exprTableView_eq hview) (hy.of_exprTableView_eq hview)
  obtain ⟨result, hresult⟩ := sOrderCmpM_run_of_success compileEnv
    blockEnv state (pure ⟨true, compare x.nfields y.nfields⟩) _ _
      rhsResult rfl hrhs
  exact ⟨result, by simpa [Ix.CompileM.compareRule] using hresult⟩

private theorem sOrderZipM_run_exact
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (f : α → α → Ix.CompileM.CompileM SOrder)
    (xs ys : List α)
    (hready : ∀ x ∈ xs, ∀ y ∈ ys, ∃ result,
      Ix.CompileM.CompileM.run compileEnv blockEnv state (f x y) =
        .ok (result, state)) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (SOrder.zipM f xs ys) = .ok (result, state) := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact ⟨_, rfl⟩
  | cons x xs ih =>
      cases ys with
      | nil => exact ⟨_, rfl⟩
      | cons y ys =>
          obtain ⟨headResult, hhead⟩ := hready x (by simp) y (by simp)
          have htail : ∀ left ∈ xs, ∀ right ∈ ys, ∃ result,
              Ix.CompileM.CompileM.run compileEnv blockEnv state
                (f left right) = .ok (result, state) := by
            intro left hleft right hright
            exact hready left (by simp [hleft]) right (by simp [hright])
          obtain ⟨tailResult, htail⟩ := ih ys htail
          unfold SOrder.zipM
          rw [run_bind, hhead]
          simp only
          cases headResult with
          | mk strong ord =>
              cases ord
              · exact ⟨_, rfl⟩
              · exact sOrderCmpM_run_of_success compileEnv blockEnv state
                  _ _ ⟨strong, .eq⟩ tailResult rfl htail
              · exact ⟨_, rfl⟩

private theorem prependSOrder_run_exact
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (head : SOrder) (tail : Ix.CompileM.CompileM SOrder)
    (tailResult : SOrder)
    (htail : Ix.CompileM.CompileM.run compileEnv blockEnv state tail =
      .ok (tailResult, state)) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (SOrder.cmpM (pure head) tail) = .ok (result, state) :=
  sOrderCmpM_run_of_success compileEnv blockEnv state (pure head) tail
    head tailResult rfl htail

private theorem sOrderCmpM_run_exact_left_view
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state next :
      Ix.CompileM.BlockState)
    (left right : Ix.CompileM.CompileM SOrder)
    (leftResult rightResult : SOrder)
    (hleft : Ix.CompileM.CompileM.run compileEnv blockEnv state left =
      .ok (leftResult, state))
    (hright : Ix.CompileM.CompileM.run compileEnv blockEnv state right =
      .ok (rightResult, next))
    (hview : exprTableView state = exprTableView origin)
    (hnext : exprTableView next = exprTableView origin) :
    ∃ result out,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (SOrder.cmpM left right) = .ok (result, out) ∧
      exprTableView out = exprTableView origin := by
  cases leftResult with
  | mk strong ord =>
      cases strong <;> cases ord
      · exact ⟨⟨false, .lt⟩, state, by
          simp [SOrder.cmpM, run_bind, hleft, run_pure], hview⟩
      · refine ⟨⟨false, rightResult.ord⟩, next, ?_, hnext⟩
        simp only [SOrder.cmpM, run_bind, hleft]
        rw [hright]
        rfl
      · exact ⟨⟨false, .gt⟩, state, by
          simp [SOrder.cmpM, run_bind, hleft, run_pure], hview⟩
      · exact ⟨⟨true, .lt⟩, state, by
          simp [SOrder.cmpM, run_bind, hleft, run_pure], hview⟩
      · exact ⟨rightResult, next, by
          simp [SOrder.cmpM, run_bind, hleft, hright], hnext⟩
      · exact ⟨⟨true, .gt⟩, state, by
          simp [SOrder.cmpM, run_bind, hleft, run_pure], hview⟩

private theorem prependSOrder_run_view
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state next :
      Ix.CompileM.BlockState)
    (head : SOrder) (tail : Ix.CompileM.CompileM SOrder)
    (tailResult : SOrder)
    (htail : Ix.CompileM.CompileM.run compileEnv blockEnv state tail =
      .ok (tailResult, next))
    (hview : exprTableView state = exprTableView origin)
    (hnext : exprTableView next = exprTableView origin) :
    ∃ result out,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (SOrder.cmpM (pure head) tail) = .ok (result, out) ∧
      exprTableView out = exprTableView origin :=
  sOrderCmpM_run_exact_left_view compileEnv blockEnv origin state next
    (pure head) tail head tailResult rfl htail hview hnext

private theorem compareCtor_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state : Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (xlvls ylvls : List Ix.Name)
    (x y : Ix.ConstructorVal)
    (hx : CompareExprReady compileEnv ctx xlvls origin x.cnst.type)
    (hy : CompareExprReady compileEnv ctx ylvls origin y.cnst.type)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compareCtor ctx xlvls ylvls x y) =
          .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
  obtain ⟨typeResult, htype⟩ := compareExpr_run_ready compileEnv blockEnv
    state ctx xlvls ylvls x.cnst.type y.cnst.type
      (hx.of_exprTableView_eq hview) (hy.of_exprTableView_eq hview)
  obtain ⟨fieldsResult, hfields⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numFields y.numFields⟩ _ typeResult
      htype
  obtain ⟨paramsResult, hparams⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numParams y.numParams⟩ _ fieldsResult
      hfields
  obtain ⟨cidxResult, hcidx⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.cidx y.cidx⟩ _ paramsResult hparams
  obtain ⟨sorder, hsorder⟩ := prependSOrder_run_exact compileEnv
    blockEnv state
      ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩
      _ cidxResult hcidx
  unfold Ix.CompileM.compareCtor
  rw [run_bind, run_getBlockState_entry]
  simp only
  generalize hcache : state.cmpCache.get?
      (Ix.CompileM.comparisonCacheKey x.cnst.name y.cnst.name) = cached
  cases cached with
  | none =>
      rw [run_bind, hsorder]
      simp only
      cases hstrong : sorder.strong with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨sorder, state, rfl, hview⟩
      | true =>
          simp only [↓reduceIte]
          let next := { state with
            cmpCache := state.cmpCache.insert
              (Ix.CompileM.comparisonCacheKey x.cnst.name y.cnst.name)
              sorder.ord }
          rw [run_bind, run_modifyBlockState_entry compileEnv blockEnv state]
          exact ⟨sorder, next, rfl, by
            simpa [next, exprTableView] using hview⟩
  | some order =>
      exact ⟨⟨true, order⟩, state, rfl, hview⟩

private theorem compareCtorZipM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (xlvls ylvls : List Ix.Name)
    (xs ys : List Ix.ConstructorVal)
    (hx : ∀ ctor ∈ xs,
      CompareExprReady compileEnv ctx xlvls origin ctor.cnst.type)
    (hy : ∀ ctor ∈ ys,
      CompareExprReady compileEnv ctx ylvls origin ctor.cnst.type)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (SOrder.zipM (Ix.CompileM.compareCtor ctx xlvls ylvls) xs ys) =
          .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
  induction xs generalizing ys state with
  | nil =>
      cases ys <;> exact ⟨_, state, rfl, hview⟩
  | cons x xs ih =>
      cases ys with
      | nil => exact ⟨_, state, rfl, hview⟩
      | cons y ys =>
          obtain ⟨headResult, headState, hhead, hheadView⟩ :=
            compareCtor_run_ready compileEnv blockEnv origin state ctx
              xlvls ylvls x y (hx x (by simp)) (hy y (by simp)) hview
          have hxtail : ∀ ctor ∈ xs,
              CompareExprReady compileEnv ctx xlvls origin
                ctor.cnst.type := by
            intro ctor hctor
            exact hx ctor (by simp [hctor])
          have hytail : ∀ ctor ∈ ys,
              CompareExprReady compileEnv ctx ylvls origin
                ctor.cnst.type := by
            intro ctor hctor
            exact hy ctor (by simp [hctor])
          obtain ⟨tailResult, tailState, htail, htailView⟩ :=
            ih headState ys hxtail hytail hheadView
          unfold SOrder.zipM
          rw [run_bind, hhead]
          simp only
          cases headResult with
          | mk strong ord =>
              cases ord
              · exact ⟨⟨strong, .lt⟩, headState, rfl, hheadView⟩
              · exact prependSOrder_run_view compileEnv blockEnv origin
                  headState tailState ⟨strong, .eq⟩
                  (SOrder.zipM
                    (Ix.CompileM.compareCtor ctx xlvls ylvls) xs ys)
                  tailResult htail hheadView htailView
              · exact ⟨⟨strong, .gt⟩, headState, rfl, hheadView⟩

private theorem compareInd_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (x y : Ix.Ind)
    (hxtype : CompareExprReady compileEnv ctx x.levelParams.toList
      origin x.type)
    (hxctors : ∀ ctor ∈ x.ctors.toList,
      CompareExprReady compileEnv ctx x.levelParams.toList
        origin ctor.cnst.type)
    (hytype : CompareExprReady compileEnv ctx y.levelParams.toList
      origin y.type)
    (hyctors : ∀ ctor ∈ y.ctors.toList,
      CompareExprReady compileEnv ctx y.levelParams.toList
        origin ctor.cnst.type)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compareInd ctx x y) = .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
  obtain ⟨ctorResult, ctorState, hctors, hctorView⟩ :=
    compareCtorZipM_run_ready compileEnv blockEnv origin state ctx
      x.levelParams.toList y.levelParams.toList x.ctors.toList
      y.ctors.toList hxctors hyctors hview
  obtain ⟨typeResult, htype⟩ := compareExpr_run_ready compileEnv
    blockEnv state ctx x.levelParams.toList y.levelParams.toList x.type
    y.type (hxtype.of_exprTableView_eq hview)
      (hytype.of_exprTableView_eq hview)
  obtain ⟨exprResult, exprState, hexprs, hexprView⟩ :=
    sOrderCmpM_run_exact_left_view compileEnv blockEnv origin state
      ctorState _ _ typeResult ctorResult htype hctors hview hctorView
  obtain ⟨ctorCountResult, ctorCountState, hctorCount,
      hctorCountView⟩ := prependSOrder_run_view compileEnv blockEnv
        origin state exprState ⟨true, compare x.ctors.size y.ctors.size⟩
        _ exprResult hexprs hview hexprView
  obtain ⟨indexResult, indexState, hindices, hindexView⟩ :=
    prependSOrder_run_view compileEnv blockEnv origin state ctorCountState
      ⟨true, compare x.numIndices y.numIndices⟩ _ ctorCountResult
      hctorCount hview hctorCountView
  obtain ⟨paramResult, paramState, hparams, hparamView⟩ :=
    prependSOrder_run_view compileEnv blockEnv origin state indexState
      ⟨true, compare x.numParams y.numParams⟩ _ indexResult
      hindices hview hindexView
  obtain ⟨result, next, hresult, hnext⟩ := prependSOrder_run_view
    compileEnv blockEnv origin state paramState
      ⟨true, compare x.levelParams.size y.levelParams.size⟩ _
      paramResult hparams hview hparamView
  exact ⟨result, next, by simpa [Ix.CompileM.compareInd] using hresult,
    hnext⟩

private theorem compareRecr_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state : Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (x y : Ix.RecursorVal)
    (hxtype : CompareExprReady compileEnv ctx x.cnst.levelParams.toList
      origin x.cnst.type)
    (hyrules : ∀ rule ∈ y.rules.toList,
      CompareExprReady compileEnv ctx y.cnst.levelParams.toList
        origin rule.rhs)
    (hytype : CompareExprReady compileEnv ctx y.cnst.levelParams.toList
      origin y.cnst.type)
    (hxrules : ∀ rule ∈ x.rules.toList,
      CompareExprReady compileEnv ctx x.cnst.levelParams.toList
        origin rule.rhs)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result, Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compareRecr ctx x y) = .ok (result, state) := by
  obtain ⟨rulesResult, hrules⟩ := sOrderZipM_run_exact compileEnv
    blockEnv state
    (Ix.CompileM.compareRule ctx x.cnst.levelParams.toList
      y.cnst.levelParams.toList)
    x.rules.toList y.rules.toList (by
      intro xrule hxrule yrule hyrule
      exact compareRule_run_ready compileEnv blockEnv origin state ctx
        x.cnst.levelParams.toList y.cnst.levelParams.toList xrule yrule
        (hxrules xrule hxrule) (hyrules yrule hyrule) hview)
  obtain ⟨typeResult, htype⟩ := compareExpr_run_ready compileEnv blockEnv
    state ctx x.cnst.levelParams.toList y.cnst.levelParams.toList
    x.cnst.type y.cnst.type (hxtype.of_exprTableView_eq hview)
      (hytype.of_exprTableView_eq hview)
  obtain ⟨exprResult, hexprs⟩ := sOrderCmpM_run_of_success compileEnv
    blockEnv state _ _ typeResult rulesResult htype hrules
  obtain ⟨kResult, hk⟩ := prependSOrder_run_exact compileEnv blockEnv
    state ⟨true, compare x.k y.k⟩ _ exprResult hexprs
  obtain ⟨minorResult, hminors⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numMinors y.numMinors⟩ _ kResult hk
  obtain ⟨motiveResult, hmotives⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numMotives y.numMotives⟩ _
      minorResult hminors
  obtain ⟨indexResult, hindices⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numIndices y.numIndices⟩ _
      motiveResult hmotives
  obtain ⟨paramResult, hparams⟩ := prependSOrder_run_exact compileEnv
    blockEnv state ⟨true, compare x.numParams y.numParams⟩ _ indexResult
      hindices
  obtain ⟨result, hresult⟩ := prependSOrder_run_exact compileEnv
    blockEnv state
      ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩
      _ paramResult hparams
  exact ⟨result, by simpa [Ix.CompileM.compareRecr] using hresult⟩

/-- Constant comparison succeeds on the explicit comparison-readiness
domain. Its only possible state effect is an insertion into the private
comparison cache, so the expression-table view remains frozen. -/
theorem compareConst_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (x y : Ix.MutConst)
    (hx : MutConstCompareReady compileEnv ctx origin x)
    (hy : MutConstCompareReady compileEnv ctx origin y)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compareConst ctx x y) = .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
  have hbody : ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compareConstBody ctx x y) = .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
    cases hx with
    | defn hxtype hxvalue =>
        cases hy with
        | defn hytype hyvalue =>
            obtain ⟨result, hresult⟩ := compareDef_run_ready compileEnv
              blockEnv origin state ctx _ _ hxtype hxvalue hytype hyvalue
              hview
            exact ⟨result, state, by
              simpa [Ix.CompileM.compareConstBody] using hresult, hview⟩
        | indc _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
        | recr _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
    | indc hxtype hxctors =>
        cases hy with
        | defn _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
        | indc hytype hyctors =>
            obtain ⟨result, next, hresult, hnext⟩ :=
              compareInd_run_ready compileEnv blockEnv origin state ctx
                _ _ hxtype hxctors hytype hyctors hview
            exact ⟨result, next, by
              simpa [Ix.CompileM.compareConstBody] using hresult, hnext⟩
        | recr _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
    | recr hxtype hxrules =>
        cases hy with
        | defn _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
        | indc _ _ => exact ⟨⟨true, .lt⟩, state, by
            simpa [Ix.CompileM.compareConstBody] using
              run_pure compileEnv blockEnv state
                (⟨true, .lt⟩ : SOrder), hview⟩
        | recr hytype hyrules =>
            obtain ⟨result, hresult⟩ := compareRecr_run_ready compileEnv
              blockEnv origin state ctx _ _ hxtype hyrules hytype hxrules
              hview
            exact ⟨result, state, by
              simpa [Ix.CompileM.compareConstBody] using hresult, hview⟩
  unfold Ix.CompileM.compareConst
  rw [run_bind, run_getBlockState_entry]
  simp only
  generalize hcache : state.cmpCache.get?
      (Ix.CompileM.comparisonCacheKey x.name y.name) = cached
  cases cached with
  | some order => exact ⟨order, state, rfl, hview⟩
  | none =>
      obtain ⟨sorder, compareState, hsorder, hcompareView⟩ := hbody
      rw [run_bind, hsorder]
      simp only
      cases hstrong : sorder.strong with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨sorder.ord, compareState, rfl, hcompareView⟩
      | true =>
          simp only [↓reduceIte]
          let next := { compareState with
            cmpCache := compareState.cmpCache.insert
              (Ix.CompileM.comparisonCacheKey x.name y.name) sorder.ord }
          rw [run_bind,
            run_modifyBlockState_entry compileEnv blockEnv compareState]
          exact ⟨sorder.ord, next, rfl, by
            simpa [next, exprTableView] using hcompareView⟩

private def BinaryActionReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin : Ix.CompileM.BlockState)
    (op : α → α → Ix.CompileM.CompileM β) : Prop :=
  ∀ state x y, exprTableView state = exprTableView origin →
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state (op x y) =
        .ok (result, next) ∧
      exprTableView next = exprTableView origin

private theorem mergeM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (cmp : α → α → Ix.CompileM.CompileM Ordering)
    (as bs : List α)
    (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.mergeM cmp as bs) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result.length = as.length + bs.length := by
  rw [List.mergeM.eq_def]
  cases as with
  | nil => exact ⟨bs, state, rfl, hview, by simp⟩
  | cons a as =>
      cases bs with
      | nil => exact ⟨a :: as, state, rfl, hview, by simp⟩
      | cons b bs =>
          obtain ⟨order, compareState, hcompare, hcompareView⟩ :=
            hcmp state a b hview
          rw [run_bind, hcompare]
          simp only
          cases hgt : order == Ordering.gt with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              obtain ⟨merged, next, hmerged, hnext, hlength⟩ :=
                mergeM_run_ready compileEnv blockEnv origin compareState
                  cmp as (b :: bs) hcmp hcompareView
              rw [run_bind, hmerged]
              exact ⟨a :: merged, next, rfl, hnext, by
                simp only [List.length_cons] at hlength ⊢
                omega⟩
          | true =>
              simp only [↓reduceIte]
              obtain ⟨merged, next, hmerged, hnext, hlength⟩ :=
                mergeM_run_ready compileEnv blockEnv origin compareState
                  cmp (a :: as) bs hcmp hcompareView
              rw [run_bind, hmerged]
              exact ⟨b :: merged, next, rfl, hnext, by
                simp only [List.length_cons] at hlength ⊢
                omega⟩
termination_by as.length + bs.length
decreasing_by all_goals simp_wf

private theorem mergePairsM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (cmp : α → α → Ix.CompileM.CompileM Ordering)
    (runs : List (List α))
    (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.mergePairsM cmp runs) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result.flatten.length = runs.flatten.length := by
  cases runs with
  | nil => exact ⟨[], state, rfl, hview, rfl⟩
  | cons first rest =>
      cases rest with
      | nil => exact ⟨[first], state, rfl, hview, rfl⟩
      | cons second tail =>
          obtain ⟨merged, mergeState, hmerge, hmergeView,
              hmergeLength⟩ :=
            mergeM_run_ready compileEnv blockEnv origin state cmp first
              second hcmp hview
          obtain ⟨mergedTail, next, htail, hnext, htailLength⟩ :=
            mergePairsM_run_ready compileEnv blockEnv origin mergeState cmp
              tail hcmp hmergeView
          unfold List.mergePairsM
          rw [run_bind, hmerge]
          simp only
          rw [run_bind, htail]
          exact ⟨merged :: mergedTail, next, rfl, hnext, by
            simp only [List.flatten_cons, List.length_append] at htailLength ⊢
            omega⟩
termination_by runs.length
decreasing_by all_goals (simp_wf; omega)

private theorem mergeAllMFuel_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (cmp : α → α → Ix.CompileM.CompileM Ordering)
    (fuel : Nat) (runs : List (List α))
    (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.mergeAllMFuel cmp fuel runs) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result.length = runs.flatten.length := by
  induction fuel generalizing state runs with
  | zero => exact ⟨runs.flatten, state, by
      rw [List.mergeAllMFuel.eq_def]
      rfl, hview, rfl⟩
  | succ fuel ih =>
      cases runs with
      | nil =>
          obtain ⟨paired, pairState, hpairs, hpairsView,
              hpairsLength⟩ :=
            mergePairsM_run_ready compileEnv blockEnv origin state cmp []
              hcmp hview
          obtain ⟨result, next, hresult, hnext, hlength⟩ :=
            ih pairState paired hpairsView
          rw [List.mergeAllMFuel.eq_def, run_bind, hpairs]
          exact ⟨result, next, hresult, hnext,
            hlength.trans hpairsLength⟩
      | cons first rest =>
          cases rest with
          | nil => exact ⟨first, state, by
              rw [List.mergeAllMFuel.eq_def]
              rfl, hview, by simp⟩
          | cons second tail =>
              obtain ⟨paired, pairState, hpairs, hpairsView,
                  hpairsLength⟩ :=
                mergePairsM_run_ready compileEnv blockEnv origin state cmp
                  (first :: second :: tail) hcmp hview
              obtain ⟨result, next, hresult, hnext, hlength⟩ :=
                ih pairState paired hpairsView
              rw [List.mergeAllMFuel.eq_def, run_bind, hpairs]
              exact ⟨result, next, hresult, hnext,
                hlength.trans hpairsLength⟩

private theorem mergeAllM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (cmp : α → α → Ix.CompileM.CompileM Ordering)
    (runs : List (List α))
    (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.mergeAllM cmp runs) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result.length = runs.flatten.length := by
  exact mergeAllMFuel_run_ready compileEnv blockEnv origin state cmp
    runs.length runs hcmp hview

mutual
  private theorem sequencesM_run_ready
      (compileEnv : Ix.CompileM.CompileEnv)
      (blockEnv : Ix.CompileM.BlockEnv) (origin state :
        Ix.CompileM.BlockState)
      (cmp : α → α → Ix.CompileM.CompileM Ordering)
      (xs : List α)
      (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
      (hview : exprTableView state = exprTableView origin) :
      ∃ result next,
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (List.sequencesM cmp xs) = .ok (result, next) ∧
        exprTableView next = exprTableView origin ∧
        result.flatten.length = xs.length := by
    rw [List.sequencesM.eq_def]
    cases xs with
    | nil => exact ⟨[[]], state, rfl, hview, rfl⟩
    | cons a rest =>
        cases rest with
        | nil => exact ⟨[[a]], state, rfl, hview, rfl⟩
        | cons b tail =>
            obtain ⟨order, compareState, hcompare, hcompareView⟩ :=
              hcmp state a b hview
            rw [run_bind, hcompare]
            simp only
            cases hgt : order == Ordering.gt with
            | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                obtain ⟨result, next, hresult, hnext, hlength⟩ :=
                  ascendingM_run_ready compileEnv blockEnv origin
                  compareState cmp b (fun ys => a :: ys) 1 tail
                  (by
                    intro ys
                    simp only [List.length_cons]
                    omega)
                  hcmp hcompareView
                exact ⟨result, next, hresult, hnext, by
                  simp only [List.length_cons] at hlength ⊢
                  omega⟩
            | true =>
                simp only [↓reduceIte]
                obtain ⟨result, next, hresult, hnext, hlength⟩ :=
                  descendingM_run_ready compileEnv blockEnv origin
                  compareState cmp b [a] tail hcmp hcompareView
                exact ⟨result, next, hresult, hnext, by
                  simp only [List.length_cons, List.length_nil] at hlength ⊢
                  omega⟩
  termination_by 2 * xs.length
  decreasing_by all_goals (simp_wf; omega)

  private theorem descendingM_run_ready
      (compileEnv : Ix.CompileM.CompileEnv)
      (blockEnv : Ix.CompileM.BlockEnv) (origin state :
        Ix.CompileM.BlockState)
      (cmp : α → α → Ix.CompileM.CompileM Ordering)
      (a : α) (as xs : List α)
      (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
      (hview : exprTableView state = exprTableView origin) :
      ∃ result next,
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (List.descendingM cmp a as xs) = .ok (result, next) ∧
        exprTableView next = exprTableView origin ∧
        result.flatten.length = (a :: as).length + xs.length := by
    rw [List.descendingM.eq_def]
    cases xs with
    | nil =>
        obtain ⟨rest, next, hrest, hnext, hlength⟩ :=
          sequencesM_run_ready
          compileEnv blockEnv origin state cmp [] hcmp hview
        rw [run_bind, hrest]
        exact ⟨(a :: as) :: rest, next, rfl, hnext, by
          simp only [List.flatten_cons, List.length_append,
            List.length_cons] at hlength ⊢
          omega⟩
    | cons b bs =>
        obtain ⟨order, compareState, hcompare, hcompareView⟩ :=
          hcmp state a b hview
        rw [run_bind, hcompare]
        simp only
        cases hgt : order == Ordering.gt with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            obtain ⟨rest, next, hrest, hnext, hlength⟩ :=
              sequencesM_run_ready
              compileEnv blockEnv origin compareState cmp (b :: bs) hcmp
                hcompareView
            rw [run_bind, hrest]
            exact ⟨(a :: as) :: rest, next, rfl, hnext, by
              simp only [List.flatten_cons, List.length_append,
                List.length_cons] at hlength ⊢
              omega⟩
        | true =>
            simp only [↓reduceIte]
            obtain ⟨result, next, hresult, hnext, hlength⟩ :=
              descendingM_run_ready compileEnv blockEnv origin
              compareState cmp b (a :: as) bs hcmp hcompareView
            exact ⟨result, next, hresult, hnext, by
              simp only [List.length_cons] at hlength ⊢
              omega⟩
  termination_by 2 * xs.length + 1
  decreasing_by all_goals simp_wf

  private theorem ascendingM_run_ready
      (compileEnv : Ix.CompileM.CompileEnv)
      (blockEnv : Ix.CompileM.BlockEnv) (origin state :
        Ix.CompileM.BlockState)
      (cmp : α → α → Ix.CompileM.CompileM Ordering)
      (a : α) (as : List α → List α) (prefixLen : Nat)
      (xs : List α)
      (has : ∀ ys, (as ys).length = prefixLen + ys.length)
      (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
      (hview : exprTableView state = exprTableView origin) :
      ∃ result next,
        Ix.CompileM.CompileM.run compileEnv blockEnv state
          (List.ascendingM cmp a as xs) = .ok (result, next) ∧
        exprTableView next = exprTableView origin ∧
        result.flatten.length = prefixLen + 1 + xs.length := by
    rw [List.ascendingM.eq_def]
    cases xs with
    | nil =>
        obtain ⟨rest, next, hrest, hnext, hlength⟩ :=
          sequencesM_run_ready
          compileEnv blockEnv origin state cmp [] hcmp hview
        rw [run_bind, hrest]
        exact ⟨as [a] :: rest, next, rfl, hnext, by
          have ha := has [a]
          simp only [List.flatten_cons, List.length_append,
            List.length_cons, List.length_nil] at ha hlength ⊢
          omega⟩
    | cons b bs =>
        obtain ⟨order, compareState, hcompare, hcompareView⟩ :=
          hcmp state a b hview
        rw [run_bind, hcompare]
        simp only
        cases hle : order != Ordering.gt with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            obtain ⟨rest, next, hrest, hnext, hlength⟩ :=
              sequencesM_run_ready
              compileEnv blockEnv origin compareState cmp (b :: bs) hcmp
                hcompareView
            rw [run_bind, hrest]
            exact ⟨as [a] :: rest, next, rfl, hnext, by
              have ha := has [a]
              simp only [List.flatten_cons, List.length_append,
                List.length_cons, List.length_nil] at ha hlength ⊢
              omega⟩
        | true =>
            simp only [↓reduceIte]
            obtain ⟨result, next, hresult, hnext, hlength⟩ :=
              ascendingM_run_ready compileEnv blockEnv origin
              compareState cmp b (fun ys => as (a :: ys))
                (prefixLen + 1) bs
                (by
                  intro ys
                  rw [has]
                  simp only [List.length_cons]
                  omega)
                hcmp hcompareView
            exact ⟨result, next, hresult, hnext, by
              simp only [List.length_cons] at hlength ⊢
              omega⟩
  termination_by 2 * xs.length + 1
  decreasing_by all_goals simp_wf
end

private theorem sortByM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (cmp : α → α → Ix.CompileM.CompileM Ordering)
    (xs : List α)
    (hcmp : BinaryActionReady compileEnv blockEnv origin cmp)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.sortByM xs cmp) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result.length = xs.length := by
  obtain ⟨runs, runsState, hruns, hrunsView, hrunsLength⟩ :=
    sequencesM_run_ready
    compileEnv blockEnv origin state cmp xs hcmp hview
  obtain ⟨result, next, hresult, hnext, hresultLength⟩ :=
    mergeAllM_run_ready
    compileEnv blockEnv origin runsState cmp runs hcmp hrunsView
  unfold List.sortByM
  rw [run_bind, hruns]
  exact ⟨result, next, hresult, hnext,
    hresultLength.trans hrunsLength⟩

private theorem reverse_flatten_length (groups : List (List α)) :
    groups.reverse.flatten.length = groups.flatten.length := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      simp only [List.reverse_cons, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append]
      rw [ih]
      omega

private theorem groupByMAux_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (eq : α → α → Ix.CompileM.CompileM Bool)
    (xs : List α) (groups : List (List α))
    (heq : BinaryActionReady compileEnv blockEnv origin eq)
    (hgroupsList : groups ≠ [])
    (hgroups : ∀ group ∈ groups, group ≠ [])
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.groupByMAux eq xs groups) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result ≠ [] ∧
      (∀ group ∈ result, group ≠ []) ∧
      result.length ≤ xs.length + groups.length ∧
      result.flatten.length = xs.length + groups.flatten.length := by
  induction xs generalizing state groups with
  | nil =>
      exact ⟨groups.reverse, state, rfl, hview, by
        simpa using hgroupsList, by
        intro group hgroup
        exact hgroups group (by simpa using hgroup), by simp,
        by simp⟩
  | cons a as ih =>
      cases groups with
      | nil => exact (hgroupsList rfl).elim
      | cons group groups =>
          cases group with
          | nil =>
              exact (hgroups [] (by simp) rfl).elim
          | cons representative members =>
              have htail : ∀ current ∈ groups, current ≠ [] := by
                intro current hcurrent
                exact hgroups current (by simp [hcurrent])
              obtain ⟨equal, compareState, hequal, hequalView⟩ :=
                heq state a representative hview
              unfold List.groupByMAux
              rw [run_bind, hequal]
              simp only
              cases equal with
              | false =>
                  simp only
                  have hacc : ∀ current ∈
                      ([a] :: (representative :: members).reverse :: groups),
                      current ≠ [] := by
                    intro current hcurrent
                    simp only [List.mem_cons] at hcurrent
                    rcases hcurrent with rfl | hcurrent
                    · simp
                    rcases hcurrent with rfl | hcurrent
                    · simp
                    exact htail current hcurrent
                  obtain ⟨result, next, hresult, hnext, hresultNonempty,
                      hnonempty, hcount, hflatten⟩ := ih compareState
                    ([a] :: (representative :: members).reverse :: groups)
                    (by simp) hacc hequalView
                  exact ⟨result, next, hresult, hnext, hresultNonempty,
                    hnonempty, by
                    simp only [List.length_cons] at hcount ⊢
                    omega, by
                    rw [hflatten]
                    simp only [List.flatten_cons, List.length_append,
                      List.length_cons, List.length_nil,
                      List.length_reverse]
                    omega⟩
              | true =>
                  simp only
                  have hacc : ∀ current ∈
                      ((a :: representative :: members) :: groups),
                      current ≠ [] := by
                    intro current hcurrent
                    simp only [List.mem_cons] at hcurrent
                    rcases hcurrent with rfl | hcurrent
                    · simp
                    exact htail current hcurrent
                  obtain ⟨result, next, hresult, hnext, hresultNonempty,
                      hnonempty, hcount, hflatten⟩ := ih compareState
                    ((a :: representative :: members) :: groups) (by simp)
                      hacc hequalView
                  exact ⟨result, next, hresult, hnext, hresultNonempty,
                    hnonempty, by
                    simp only [List.length_cons] at hcount ⊢
                    omega, by
                    rw [hflatten]
                    simp only [List.flatten_cons, List.length_append,
                      List.length_cons]
                    omega⟩

private theorem groupByM_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (eq : α → α → Ix.CompileM.CompileM Bool)
    (xs : List α)
    (heq : BinaryActionReady compileEnv blockEnv origin eq)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (List.groupByM eq xs) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      (xs ≠ [] → result ≠ []) ∧
      (∀ group ∈ result, group ≠ []) ∧
      result.length ≤ xs.length ∧
      result.flatten.length = xs.length := by
  cases xs with
  | nil => exact ⟨[], state, rfl, hview, by simp, by simp, by simp, rfl⟩
  | cons a as =>
      unfold List.groupByM
      obtain ⟨result, next, hresult, hnext, hresultNonempty, hnonempty,
          hcount, hflatten⟩ :=
        groupByMAux_run_ready compileEnv blockEnv origin state eq as [[a]]
          heq (by simp) (by simp) hview
      exact ⟨result, next, hresult, hnext, fun _ => hresultNonempty,
        hnonempty, by
        simp only [List.length_cons, List.length_nil] at hcount ⊢
        omega, by
        simp only [List.flatten_cons, List.flatten_nil,
          List.append_nil, List.length_cons, List.length_nil] at hflatten ⊢
        omega⟩

private theorem insertSortMutConstMemberByName_length
    {sources : List Ix.MutConst}
    (source : Ix.CompileM.SortMutConstMember sources)
    (members : List (Ix.CompileM.SortMutConstMember sources)) :
    (Ix.CompileM.insertSortMutConstMemberByName source members).length =
      members.length + 1 := by
  induction members with
  | nil => rfl
  | cons current rest ih =>
      rw [Ix.CompileM.insertSortMutConstMemberByName]
      by_cases horder : compare source.1.name current.1.name == .gt
      · rw [if_pos horder]
        simp only [List.length_cons, ih]
      · rw [if_neg horder]
        simp

private theorem sortMutConstMembersByName_length
    {sources : List Ix.MutConst}
    (members : List (Ix.CompileM.SortMutConstMember sources)) :
    (Ix.CompileM.sortMutConstMembersByName members).length =
      members.length := by
  induction members with
  | nil => rfl
  | cons source rest ih =>
      rw [Ix.CompileM.sortMutConstMembersByName,
        insertSortMutConstMemberByName_length, ih]
      simp

private theorem map_sortMutConstMembersByName_flatten_length
    {sources : List Ix.MutConst}
    (groups : List (List (Ix.CompileM.SortMutConstMember sources))) :
    (groups.map Ix.CompileM.sortMutConstMembersByName).flatten.length =
      groups.flatten.length := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [sortMutConstMembersByName_length, ih]

/-- Source-local domain for every comparison context that bounded partition
refinement may construct. -/
def MutConstSortReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (origin : Ix.CompileM.BlockState) (sources : List Ix.MutConst) : Prop :=
  ∀ ctx source, source ∈ sources →
    MutConstCompareReady compileEnv ctx origin source

private theorem eqConst_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (ctx : Ix.MutCtx) (x y : Ix.MutConst)
    (hx : MutConstCompareReady compileEnv ctx origin x)
    (hy : MutConstCompareReady compileEnv ctx origin y)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.eqConst ctx x y) = .ok (result, next) ∧
      exprTableView next = exprTableView origin := by
  obtain ⟨order, next, horder, hnext⟩ := compareConst_run_ready
    compileEnv blockEnv origin state ctx x y hx hy hview
  unfold Ix.CompileM.eqConst
  rw [run_bind, horder]
  exact ⟨order == .eq, next, rfl, hnext⟩

private theorem refineMutConstClass_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (sources : List Ix.MutConst) (ctx : Ix.MutCtx)
    (members : List (Ix.CompileM.SortMutConstMember sources))
    (hready : MutConstSortReady compileEnv origin sources)
    (hmembers : members ≠ [])
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.refineMutConstClass ctx members) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      result ≠ [] ∧
      (∀ group ∈ result, group ≠ []) ∧
      result.length ≤ members.length ∧
      result.flatten.length = members.length := by
  cases members with
  | nil => exact (hmembers rfl).elim
  | cons first rest =>
      cases rest with
      | nil => exact ⟨[[first]], state, rfl, hview, by simp, by simp,
          by simp, rfl⟩
      | cons second tail =>
          have hcmp : BinaryActionReady compileEnv blockEnv origin
              (fun x y : Ix.CompileM.SortMutConstMember sources =>
                Ix.CompileM.compareConst ctx x.1 y.1) := by
            intro next x y hnext
            exact compareConst_run_ready compileEnv blockEnv origin next ctx
              x.1 y.1 (hready ctx x.1 x.property)
                (hready ctx y.1 y.property) hnext
          obtain ⟨sorted, sortState, hsort, hsortView, hsortLength⟩ :=
            sortByM_run_ready compileEnv blockEnv origin state
              (fun x y : Ix.CompileM.SortMutConstMember sources =>
                Ix.CompileM.compareConst ctx x.1 y.1)
              (first :: second :: tail) hcmp hview
          have heq : BinaryActionReady compileEnv blockEnv origin
              (fun x y : Ix.CompileM.SortMutConstMember sources =>
                Ix.CompileM.eqConst ctx x.1 y.1) := by
            intro next x y hnext
            exact eqConst_run_ready compileEnv blockEnv origin next ctx x.1
              y.1 (hready ctx x.1 x.property)
                (hready ctx y.1 y.property) hnext
          obtain ⟨groups, groupState, hgroups, hgroupsView,
              hgroupsNonemptyOf, hgroupNonempty, hgroupCount,
              hgroupFlatten⟩ := groupByM_run_ready compileEnv blockEnv
                origin sortState
                (fun x y : Ix.CompileM.SortMutConstMember sources =>
                  Ix.CompileM.eqConst ctx x.1 y.1)
                sorted heq hsortView
          have hsortedNonempty : sorted ≠ [] := by
            intro hempty
            rw [hempty] at hsortLength
            simp only [List.length_nil, List.length_cons] at hsortLength
            omega
          have hgroupsNonempty : groups ≠ [] :=
            hgroupsNonemptyOf hsortedNonempty
          let canonical := groups.map Ix.CompileM.sortMutConstMembersByName
          have hcanonicalNonempty : canonical ≠ [] := by
            simpa [canonical] using hgroupsNonempty
          have hcanonicalGroups : ∀ group ∈ canonical, group ≠ [] := by
            intro group hgroup
            simp only [canonical, List.mem_map] at hgroup
            obtain ⟨original, horiginal, rfl⟩ := hgroup
            intro hempty
            have hlength := sortMutConstMembersByName_length original
            rw [hempty] at hlength
            apply hgroupNonempty original horiginal
            cases original with
            | nil => rfl
            | cons source rest =>
                simp only [List.length_nil, List.length_cons] at hlength
                omega
          unfold Ix.CompileM.refineMutConstClass
          rw [run_bind, hsort]
          simp only
          rw [run_bind, hgroups]
          exact ⟨canonical, groupState, rfl, hgroupsView,
            hcanonicalNonempty, hcanonicalGroups, by
              simpa [canonical, hsortLength] using hgroupCount, by
              rw [map_sortMutConstMembersByName_flatten_length,
                hgroupFlatten, hsortLength]⟩

private theorem refineMutConstClasses_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (sources : List Ix.MutConst) (ctx : Ix.MutCtx)
    (classes : List (List (Ix.CompileM.SortMutConstMember sources)))
    (hready : MutConstSortReady compileEnv origin sources)
    (hclasses : ∀ group ∈ classes, group ≠ [])
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.refineMutConstClasses ctx classes) =
          .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      (∀ group ∈ result, group ≠ []) ∧
      classes.length ≤ result.length ∧
      result.length ≤ classes.flatten.length ∧
      result.flatten.length = classes.flatten.length := by
  induction classes generalizing state with
  | nil => exact ⟨[], state, rfl, hview, by simp, by simp, by simp, rfl⟩
  | cons current rest ih =>
      have hcurrent : current ≠ [] := hclasses current (by simp)
      have hrest : ∀ group ∈ rest, group ≠ [] := by
        intro group hgroup
        exact hclasses group (by simp [hgroup])
      obtain ⟨headGroups, headState, hhead, hheadView,
          hheadListNonempty, hheadNonempty, hheadCount, hheadFlatten⟩ :=
        refineMutConstClass_run_ready compileEnv blockEnv origin state
          sources ctx current hready hcurrent hview
      obtain ⟨tailGroups, next, htail, htailView, htailNonempty,
          htailLower, htailUpper, htailFlatten⟩ :=
        ih headState hrest hheadView
      unfold Ix.CompileM.refineMutConstClasses
      rw [run_bind, hhead]
      simp only
      rw [run_bind, htail]
      exact ⟨headGroups ++ tailGroups, next, rfl, htailView, by
        intro group hgroup
        simp only [List.mem_append] at hgroup
        exact hgroup.elim (hheadNonempty group) (htailNonempty group), by
        have hheadPositive : 0 < headGroups.length := by
          cases headGroups with
          | nil => exact (hheadListNonempty rfl).elim
          | cons group groups => simp
        simp only [List.length_cons, List.length_append]
        omega, by
        simp only [List.flatten_cons, List.length_append]
        omega, by
        simp only [List.flatten_cons, List.flatten_append,
          List.length_append]
        omega⟩

private theorem nonemptyClasses_length_le_flatten
    (classes : List (List α))
    (hclasses : ∀ group ∈ classes, group ≠ []) :
    classes.length ≤ classes.flatten.length := by
  induction classes with
  | nil => simp
  | cons group rest ih =>
      have hgroup : group ≠ [] := hclasses group (by simp)
      have hrest : ∀ current ∈ rest, current ≠ [] := by
        intro current hcurrent
        exact hclasses current (by simp [hcurrent])
      have hgroupPositive : 0 < group.length := by
        cases group with
        | nil => exact (hgroup rfl).elim
        | cons source sources => simp
      have htail := ih hrest
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

private theorem sortConstsLoop_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin state :
      Ix.CompileM.BlockState)
    (sources : List Ix.MutConst) (fuel : Nat)
    (classes : List (List (Ix.CompileM.SortMutConstMember sources)))
    (hready : MutConstSortReady compileEnv origin sources)
    (hclasses : ∀ group ∈ classes, group ≠ [])
    (hflatten : classes.flatten.length = sources.length)
    (hbudget : sources.length < classes.length + fuel)
    (hview : exprTableView state = exprTableView origin) :
    ∃ result next,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.sortConstsLoop fuel classes) = .ok (result, next) ∧
      exprTableView next = exprTableView origin ∧
      (∀ group ∈ result, group ≠ []) ∧
      result.flatten.length = sources.length := by
  induction fuel generalizing state classes with
  | zero =>
      have hupper := nonemptyClasses_length_le_flatten classes hclasses
      rw [hflatten] at hupper
      simp only [Nat.add_zero] at hbudget
      omega
  | succ fuel ih =>
      obtain ⟨refined, refineState, hrefine, hrefineView,
          hrefinedNonempty, hlower, _hupper, hrefinedFlatten⟩ :=
        refineMutConstClasses_run_ready compileEnv blockEnv origin state
          sources (Ix.CompileM.sortMutConstCtx classes) classes hready
          hclasses hview
      have hrefinedSource : refined.flatten.length = sources.length :=
        hrefinedFlatten.trans hflatten
      rw [Ix.CompileM.sortConstsLoop, run_bind, hrefine]
      simp only
      cases hsame : classes.length == refined.length with
      | true =>
          simp only [↓reduceIte]
          exact ⟨refined, refineState, rfl, hrefineView,
            hrefinedNonempty, hrefinedSource⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hstrict : classes.length < refined.length := by
            have hne : classes.length ≠ refined.length := by
              intro heq
              rw [heq] at hsame
              simp at hsame
            omega
          have hnextBudget :
              sources.length < refined.length + fuel := by
            simp only [Nat.add_succ] at hbudget
            omega
          exact ih refineState refined hrefinedNonempty hrefinedSource
            hnextBudget hrefineView

private theorem findConst_run_of_get_entry
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) (constInfo : Ix.ConstantInfo)
    (hget : compileEnv.env.get? name = some constInfo) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.findConst name) = .ok (constInfo, state) := by
  unfold Ix.CompileM.findConst
  rw [run_bind, run_getCompileEnv_entry]
  simp only
  rw [hget]
  rfl

theorem collectMutConstConstructors_run_of_lookup
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (names : List Ix.Name) (ctorVals : List Ix.ConstructorVal)
    (acc : Array Ix.ConstructorVal)
    (hlookup : List.Forall₂ (fun name ctor =>
      compileEnv.env.get? name = some (.ctorInfo ctor)) names ctorVals) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectMutConstConstructors names acc) =
      .ok (acc ++ ctorVals.toArray, state) := by
  induction hlookup generalizing acc with
  | nil =>
      simpa [Ix.CompileM.collectMutConstConstructors] using
        run_pure compileEnv blockEnv state acc
  | cons hget rest ih =>
      unfold Ix.CompileM.collectMutConstConstructors
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      simp only
      rw [ih (acc := acc.push _)]
      congr 2
      rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem mutConstMkIndc_run_of_lookup
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal
      ctorVals) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.MutConst.mkIndc inductiveVal) =
      .ok (Ix.MutConst.fromInductiveVal inductiveVal ctorVals, state) := by
  unfold Ix.CompileM.MutConst.mkIndc
  rw [run_bind,
    collectMutConstConstructors_run_of_lookup compileEnv blockEnv state
      inductiveVal.ctors.toList ctorVals.toList #[] hlookup]
  simpa [Ix.MutConst.fromInductiveVal] using
    run_pure compileEnv blockEnv state
      (Ix.MutConst.fromInductiveVal inductiveVal ctorVals)

/-- Exact environment evidence for resolving one SCC name into the optional
mutual-source grammar. Axioms, quotients, and constructor names match the
production filter and contribute no member. -/
inductive MutConstSourceLookup (compileEnv : Ix.CompileM.CompileEnv)
    (name : Ix.Name) : Option Ix.MutConst → Prop where
  | indc {inductiveVal : Ix.InductiveVal}
      {ctorVals : Array Ix.ConstructorVal} :
      compileEnv.env.get? name = some (.inductInfo inductiveVal) →
      InductiveConstructorLookup compileEnv inductiveVal ctorVals →
      MutConstSourceLookup compileEnv name
        (some (Ix.MutConst.fromInductiveVal inductiveVal ctorVals))
  | defn {definitionVal : Ix.DefinitionVal} :
      compileEnv.env.get? name = some (.defnInfo definitionVal) →
      MutConstSourceLookup compileEnv name
        (some (Ix.MutConst.fromDefinitionVal definitionVal))
  | thm {theoremVal : Ix.TheoremVal} :
      compileEnv.env.get? name = some (.thmInfo theoremVal) →
      MutConstSourceLookup compileEnv name
        (some (Ix.MutConst.fromTheoremVal theoremVal))
  | opaq {opaqueVal : Ix.OpaqueVal} :
      compileEnv.env.get? name = some (.opaqueInfo opaqueVal) →
      MutConstSourceLookup compileEnv name
        (some (Ix.MutConst.fromOpaqueVal opaqueVal))
  | recr {recursorVal : Ix.RecursorVal} :
      compileEnv.env.get? name = some (.recInfo recursorVal) →
      MutConstSourceLookup compileEnv name (some (.recr recursorVal))
  | axio {axiomVal : Ix.AxiomVal} :
      compileEnv.env.get? name = some (.axiomInfo axiomVal) →
      MutConstSourceLookup compileEnv name none
  | quot {quotientVal : Ix.QuotVal} :
      compileEnv.env.get? name = some (.quotInfo quotientVal) →
      MutConstSourceLookup compileEnv name none
  | ctor {constructorVal : Ix.ConstructorVal} :
      compileEnv.env.get? name = some (.ctorInfo constructorVal) →
      MutConstSourceLookup compileEnv name none

theorem resolveMutConst_run_of_lookup
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) {source? : Option Ix.MutConst}
    (hlookup : MutConstSourceLookup compileEnv name source?) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.resolveMutConst? name) = .ok (source?, state) := by
  cases hlookup with
  | @indc inductiveVal ctorVals hget hctors =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      simp only [Ix.CompileM.collectMutConst?]
      rw [run_bind, mutConstMkIndc_run_of_lookup compileEnv blockEnv state
        inductiveVal ctorVals hctors]
      exact run_pure compileEnv blockEnv state _
  | defn hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | thm hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | opaq hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | recr hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | axio hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | quot hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _
  | ctor hget =>
      unfold Ix.CompileM.resolveMutConst?
      rw [run_bind,
        findConst_run_of_get_entry compileEnv blockEnv state _ _ hget]
      exact run_pure compileEnv blockEnv state _

theorem collectMutConsts_run_of_lookups
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (names : List Ix.Name) (sources : List (Option Ix.MutConst))
    (acc : Array Ix.MutConst)
    (hlookups : List.Forall₂ (MutConstSourceLookup compileEnv) names
      sources) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectMutConsts names acc) =
      .ok (acc ++ (sources.filterMap id).toArray, state) := by
  induction hlookups generalizing acc with
  | nil =>
      simpa [Ix.CompileM.collectMutConsts] using
        run_pure compileEnv blockEnv state acc
  | @cons name source? names sources hlookup hlookups ih =>
      unfold Ix.CompileM.collectMutConsts
      rw [run_bind, resolveMutConst_run_of_lookup compileEnv blockEnv state
        name hlookup]
      simp only
      cases source? with
      | none =>
          change Ix.CompileM.CompileM.run compileEnv blockEnv state
              (Ix.CompileM.collectMutConsts names acc) =
            .ok (acc ++ (sources.filterMap id).toArray, state)
          exact ih (acc := acc)
      | some source =>
          rw [ih (acc := acc.push source)]
          congr 2
          change acc.push source ++ (sources.filterMap id).toArray =
            acc ++ (source :: sources.filterMap id).toArray
          rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem collectedMutConstSourceCount_lt
    (compileEnv : Ix.CompileM.CompileEnv)
    (all : Ix.Set Ix.Name) (resolved : List (Option Ix.MutConst))
    (hlookups : List.Forall₂ (MutConstSourceLookup compileEnv)
      all.toList resolved)
    (hallCount : all.toList.length < UInt64.size) :
    (resolved.filterMap id).length < UInt64.size := by
  have forall₂Length : ∀ {names : List Ix.Name}
      {items : List (Option Ix.MutConst)},
      List.Forall₂ (MutConstSourceLookup compileEnv) names items →
        names.length = items.length := by
    intro names items hrelation
    induction hrelation with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have hlength : all.toList.length = resolved.length :=
    forall₂Length hlookups
  exact Nat.lt_of_le_of_lt (List.length_filterMap_le id resolved) (by
    rw [← hlength]
    exact hallCount)

/-- Structural postcondition exported by the bounded mutual classifier. -/
structure SortedMutConstClassesWF (sources : List Ix.MutConst)
    (classes : List (List Ix.MutConst)) : Prop where
  nonempty : ∀ constClass ∈ classes, constClass ≠ []
  count : classes.length ≤ sources.length
  members : ∀ constClass ∈ classes, ∀ source ∈ constClass,
    source ∈ sources

theorem SortedMutConstClassesWF.members_of
    {sources : List Ix.MutConst} {classes : List (List Ix.MutConst)}
    (hclasses : SortedMutConstClassesWF sources classes)
    (property : Ix.MutConst → Prop)
    (hsources : ∀ source ∈ sources, property source) :
    ∀ constClass ∈ classes, ∀ source ∈ constClass,
      property source := by
  intro constClass hclass source hsource
  exact hsources source (hclasses.members constClass hclass source hsource)

theorem nonemptyMutConstClassCount_eq_length
    (classes : List (List Ix.MutConst))
    (hnonempty : ∀ constClass ∈ classes, constClass ≠ []) :
    nonemptyMutConstClassCount classes = classes.length := by
  induction classes with
  | nil => rfl
  | cons constClass rest ih =>
      have hhead : constClass ≠ [] := hnonempty constClass (by simp)
      have hrest : ∀ current ∈ rest, current ≠ [] := by
        intro current hmem
        exact hnonempty current (by simp [hmem])
      cases constClass with
      | nil => exact (hhead rfl).elim
      | cons source sources =>
          simp only [nonemptyMutConstClassCount, List.length_cons]
          rw [ih hrest]

theorem SortedMutConstClassesWF.nonemptyCount_lt
    {sources : List Ix.MutConst} {classes : List (List Ix.MutConst)}
    (hclasses : SortedMutConstClassesWF sources classes)
    (hsourceCount : sources.length < UInt64.size) :
    nonemptyMutConstClassCount classes < UInt64.size := by
  rw [nonemptyMutConstClassCount_eq_length classes hclasses.nonempty]
  exact Nat.lt_of_le_of_lt hclasses.count hsourceCount

/-- Any successful bounded classification has only nonempty classes, no more
classes than source members, and no synthesized members. The last property is
carried by the sorter's erased source-membership tags rather than by a
permutation proof about the mergesort implementation. -/
theorem sortConsts_run_classesWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state sortState : Ix.CompileM.BlockState)
    (sources : List Ix.MutConst) (classes : List (List Ix.MutConst))
    (hsort : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.sortConsts sources) = .ok (classes, sortState)) :
    SortedMutConstClassesWF sources classes := by
  unfold Ix.CompileM.sortConsts at hsort
  rw [run_bind] at hsort
  generalize Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.sortConstsLoop (sources.length + 1)
        [Ix.CompileM.sortMutConstMembersByName sources.attach]) =
          sortResult at hsort
  cases sortResult with
  | error err => simp at hsort
  | ok result =>
      rcases result with ⟨taggedClasses, taggedState⟩
      simp only at hsort
      let mappedClasses := taggedClasses.map fun constClass =>
        constClass.map fun source => source.1
      change Ix.CompileM.CompileM.run compileEnv blockEnv taggedState
        (if mappedClasses.any (fun constClass => constClass.isEmpty) then
          throw (.invalidMutualBlock "empty class after sortConsts")
        else if sources.length < mappedClasses.length then
          throw (.invalidMutualBlock "too many classes after sortConsts")
        else pure mappedClasses) = .ok (classes, sortState) at hsort
      by_cases hempty : mappedClasses.any
          (fun constClass => constClass.isEmpty) = true
      · rw [if_pos hempty,
          run_throw compileEnv blockEnv taggedState] at hsort
        contradiction
      · rw [if_neg hempty] at hsort
        by_cases htooMany : sources.length < mappedClasses.length
        · rw [if_pos htooMany,
            run_throw compileEnv blockEnv taggedState] at hsort
          contradiction
        · rw [if_neg htooMany,
            run_pure compileEnv blockEnv taggedState] at hsort
          have hpair : (mappedClasses, taggedState) =
              (classes, sortState) := Except.ok.inj hsort
          have hclasses : mappedClasses = classes :=
            congrArg Prod.fst hpair
          rw [← hclasses]
          refine ⟨?_, ?_, ?_⟩
          · intro constClass hclass heq
            have hany : mappedClasses.any
                (fun current => current.isEmpty) = true := by
              apply List.any_eq_true.mpr
              exact ⟨constClass, hclass, by simp [heq]⟩
            exact hempty hany
          · simpa using Nat.le_of_not_gt htooMany
          · intro constClass hclass source hsource
            simp only [mappedClasses, List.mem_map] at hclass
            obtain ⟨taggedClass, _htaggedClass, rfl⟩ := hclass
            simp only [List.mem_map] at hsource
            obtain ⟨taggedSource, _htaggedSource, rfl⟩ := hsource
            exact taggedSource.property

/-- Bounded classification is constructively executable from source-local
comparison readiness. Every recursive round strictly consumes the finite
class-count budget; the result preserves the frozen expression-table view. -/
theorem sortConsts_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (sources : List Ix.MutConst)
    (hready : MutConstSortReady compileEnv state sources)
    (hsources : sources ≠ []) :
    ∃ classes sortState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.sortConsts sources) = .ok (classes, sortState) ∧
      exprTableView sortState = exprTableView state ∧
      SortedMutConstClassesWF sources classes := by
  let initial := Ix.CompileM.sortMutConstMembersByName sources.attach
  have hinitialNonempty : initial ≠ [] := by
    intro hempty
    have hlength := sortMutConstMembersByName_length sources.attach
    simp only [List.length_attach] at hlength
    have hempty' : Ix.CompileM.sortMutConstMembersByName sources.attach =
        [] := by simpa [initial] using hempty
    rw [hempty'] at hlength
    simp only [List.length_nil] at hlength
    apply hsources
    cases sources with
    | nil => rfl
    | cons source rest =>
        simp only [List.length_cons] at hlength
        omega
  have hinitialClasses : ∀ group ∈ [initial], group ≠ [] := by
    simpa using hinitialNonempty
  have hinitialFlatten : [initial].flatten.length = sources.length := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact sortMutConstMembersByName_length sources.attach |>.trans
      List.length_attach
  have hinitialBudget :
      sources.length < [initial].length + (sources.length + 1) := by
    simp
    omega
  obtain ⟨taggedClasses, taggedState, hloop, hloopView,
      htaggedNonempty, htaggedFlatten⟩ :=
    sortConstsLoop_run_ready compileEnv blockEnv state state sources
      (sources.length + 1) [initial] hready hinitialClasses
      hinitialFlatten hinitialBudget rfl
  let classes := taggedClasses.map fun constClass =>
    constClass.map fun source => source.1
  have hclassesNonempty : ∀ constClass ∈ classes,
      constClass ≠ [] := by
    intro constClass hclass
    simp only [classes, List.mem_map] at hclass
    obtain ⟨taggedClass, htaggedClass, rfl⟩ := hclass
    have htagged := htaggedNonempty taggedClass htaggedClass
    cases taggedClass with
    | nil => exact (htagged rfl).elim
    | cons source rest => simp
  have hclassCount : classes.length ≤ sources.length := by
    have hcount := nonemptyClasses_length_le_flatten taggedClasses
      htaggedNonempty
    rw [htaggedFlatten] at hcount
    simpa [classes] using hcount
  have hempty : classes.any (fun constClass => constClass.isEmpty) ≠
      true := by
    intro hany
    obtain ⟨constClass, hclass, hisEmpty⟩ :=
      List.any_eq_true.mp hany
    apply hclassesNonempty constClass hclass
    simpa using hisEmpty
  have htooMany : ¬ sources.length < classes.length :=
    Nat.not_lt.mpr hclassCount
  have hsort : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.sortConsts sources) = .ok (classes, taggedState) := by
    unfold Ix.CompileM.sortConsts
    change Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.sortConstsLoop (sources.length + 1) [initial] >>=
        fun taggedClasses =>
          let mapped := taggedClasses.map fun constClass =>
            constClass.map fun source => source.1
          if mapped.any (fun constClass => constClass.isEmpty) then
            throw (.invalidMutualBlock "empty class after sortConsts")
          else if sources.length < mapped.length then
            throw (.invalidMutualBlock "too many classes after sortConsts")
          else pure mapped) = .ok (classes, taggedState)
    rw [run_bind, hloop]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv taggedState
      (if classes.any (fun constClass => constClass.isEmpty) then
        throw (.invalidMutualBlock "empty class after sortConsts")
      else if sources.length < classes.length then
        throw (.invalidMutualBlock "too many classes after sortConsts")
      else pure classes) = .ok (classes, taggedState)
    rw [if_neg hempty, if_neg htooMany]
    rfl
  exact ⟨classes, taggedState, hsort, hloopView,
    sortConsts_run_classesWF compileEnv blockEnv state taggedState sources
      classes hsort⟩

/-- The production sorter restores its incoming block state after the private
comparison-cache phase. -/
theorem sortConstsIsolated_run_of_sort
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state sortState : Ix.CompileM.BlockState)
    (sources : List Ix.MutConst) (classes : List (List Ix.MutConst))
    (hsort : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.sortConsts sources) = .ok (classes, sortState)) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.sortConstsIsolated sources) = .ok (classes, state) := by
  unfold Ix.CompileM.sortConstsIsolated
  rw [run_bind, run_getBlockState_entry]
  simp only
  rw [run_bind, hsort]
  simp only
  rw [run_bind,
    run_restoreBlockState_entry compileEnv blockEnv sortState state]
  exact run_pure compileEnv blockEnv state classes

/-- The proof-visible non-singleton SCC pipeline: once collection and
classification have produced source classes, the member-local uniform
readiness theorem closes the exact production `compileMutualConstants`
driver.  The two prefix executions remain explicit boundaries for the next
sorting-refinement layer. -/
theorem compileMutualConstants_run_of_collected_sorted_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state collectState sortState : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (all : Ix.Set Ix.Name) (sources : Array Ix.MutConst)
    (classes : List (List Ix.MutConst)) (params : List Ix.Name)
    (hcollect : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectMutConsts all.toList #[]) =
        .ok (sources, collectState))
    (hsort : Ix.CompileM.CompileM.run compileEnv blockEnv collectState
      (Ix.CompileM.sortConsts sources.toList) = .ok (classes, sortState))
    (hexprCache : collectState.exprCache = {})
    (hcanonCache : CanonUnivCacheWF collectState)
    (hrefTable : PreseedRefTableWF collectState)
    (hunivTable : PreseedUnivTableWF collectState)
    (huniform : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstUniformPreseedParams params source)
    (hready : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (mutualCompileBlockEnv blockEnv classes) input.2)
        levelSupport (preseedContextStartState collectState) input.1)
    (htableBound : InputPreseedSourceBound
      (mutualCompileBlockEnv blockEnv classes) collectState
      (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileMutualConstants all) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  obtain ⟨result, finalState, hblock, hcodec⟩ :=
    compileMutualBlock_run_member_uniform_ready_codecWF compileEnv blockEnv
      collectState hfree hclosed hlevelFaithful hexprFaithful classes params
      hexprCache hcanonCache hrefTable hunivTable huniform hready htableBound
      hmembers hcount
  refine ⟨result, finalState, ?_, hcodec⟩
  unfold Ix.CompileM.compileMutualConstants
  rw [run_bind, hcollect]
  simp only
  rw [run_bind, sortConstsIsolated_run_of_sort compileEnv blockEnv
    collectState sortState sources.toList classes hsort]
  exact hblock

/-- Codec safety at the public named-constant compiler entry for a
non-singleton SCC, factored over the explicit collection and sorting prefix. -/
theorem compileConstant_run_mutual_of_collected_sorted_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state collectState sortState : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (name : Ix.Name) (constInfo : Ix.ConstantInfo)
    (sources : Array Ix.MutConst)
    (classes : List (List Ix.MutConst)) (params : List Ix.Name)
    (hlookup : compileEnv.env.get? name = some constInfo)
    (hmulti : (blockEnv.all.size == 1) = false)
    (hcollect : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectMutConsts blockEnv.all.toList #[]) =
        .ok (sources, collectState))
    (hsort : Ix.CompileM.CompileM.run compileEnv blockEnv collectState
      (Ix.CompileM.sortConsts sources.toList) = .ok (classes, sortState))
    (hexprCache : collectState.exprCache = {})
    (hcanonCache : CanonUnivCacheWF collectState)
    (hrefTable : PreseedRefTableWF collectState)
    (hunivTable : PreseedUnivTableWF collectState)
    (huniform : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstUniformPreseedParams params source)
    (hready : ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (mutualCompileBlockEnv blockEnv classes) input.2)
        levelSupport (preseedContextStartState collectState) input.1)
    (htableBound : InputPreseedSourceBound
      (mutualCompileBlockEnv blockEnv classes) collectState
      (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source)
    (hcount : nonemptyMutConstClassCount classes < UInt64.size) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstant name) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  obtain ⟨result, finalState, hmutual, hcodec⟩ :=
    compileMutualConstants_run_of_collected_sorted_codecWF compileEnv
      blockEnv state collectState sortState hfree hclosed hlevelFaithful
      hexprFaithful blockEnv.all sources classes params hcollect hsort
      hexprCache hcanonCache hrefTable hunivTable huniform hready htableBound
      hmembers hcount
  refine ⟨result, finalState, ?_, hcodec⟩
  unfold Ix.CompileM.compileConstant
  rw [run_bind, findConst_run_of_get_entry compileEnv blockEnv state name
    constInfo hlookup]
  simp only
  rw [run_bind, run_getBlockEnv_entry]
  simp only
  simp only [hmulti, Bool.false_eq_true, ↓reduceIte]
  exact hmutual

/-- The named non-singleton compiler entry with SCC member collection derived
from explicit environment lookup evidence. Bounded classification is
constructed from source-local comparison readiness; all downstream preseed
obligations are supplied uniformly for the structurally valid partition it
produces. -/
theorem compileConstant_run_mutual_of_lookup_sorted_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (name : Ix.Name) (constInfo : Ix.ConstantInfo)
    (resolved : List (Option Ix.MutConst))
    (params : List Ix.Name)
    (hlookup : compileEnv.env.get? name = some constInfo)
    (hmulti : (blockEnv.all.size == 1) = false)
    (hlookups : List.Forall₂ (MutConstSourceLookup compileEnv)
      blockEnv.all.toList resolved)
    (hallCount : blockEnv.all.toList.length < UInt64.size)
    (hsortReady : MutConstSortReady compileEnv state
      (resolved.filterMap id))
    (hsources : resolved.filterMap id ≠ [])
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (huniform : ∀ source ∈ resolved.filterMap id,
      MutConstUniformPreseedParams params source)
    (hready : ∀ classes,
      SortedMutConstClassesWF (resolved.filterMap id) classes →
      ∀ input ∈ Ix.CompileM.mutualPreseedInputs classes,
        PreseedReady compileEnv
          (preseedContextBlockEnv
            (mutualCompileBlockEnv blockEnv classes) input.2)
          levelSupport (preseedContextStartState state) input.1)
    (htableBound : ∀ classes,
      SortedMutConstClassesWF (resolved.filterMap id) classes →
      InputPreseedSourceBound
        (mutualCompileBlockEnv blockEnv classes) state
        (Ix.CompileM.mutualPreseedInputs classes))
    (hmembers : ∀ source ∈ resolved.filterMap id,
      MutConstOrdinaryBounds source) :
    ∃ result finalState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstant name) =
        .ok (result, finalState) ∧
      BlockResultCodecWF result := by
  have hsourceCount : (resolved.filterMap id).length < UInt64.size :=
    collectedMutConstSourceCount_lt compileEnv blockEnv.all resolved
      hlookups hallCount
  obtain ⟨classes, sortState, hsort, _hsortView, hclasses⟩ :=
    sortConsts_run_ready compileEnv blockEnv state (resolved.filterMap id)
      hsortReady hsources
  have huniform' : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstUniformPreseedParams params source :=
    hclasses.members_of (MutConstUniformPreseedParams params) huniform
  have hmembers' : ∀ constClass ∈ classes, ∀ source ∈ constClass,
      MutConstOrdinaryBounds source :=
    hclasses.members_of MutConstOrdinaryBounds hmembers
  have hcount : nonemptyMutConstClassCount classes < UInt64.size :=
    hclasses.nonemptyCount_lt hsourceCount
  have hcollect : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectMutConsts blockEnv.all.toList #[]) =
        .ok ((resolved.filterMap id).toArray, state) := by
    simpa using collectMutConsts_run_of_lookups compileEnv blockEnv state
      blockEnv.all.toList resolved #[] hlookups
  exact compileConstant_run_mutual_of_collected_sorted_codecWF compileEnv
    blockEnv state state sortState hfree hclosed hlevelFaithful
    hexprFaithful name constInfo (resolved.filterMap id).toArray classes
    params hlookup hmulti hcollect hsort hexprCache hcanonCache hrefTable
    hunivTable huniform' (hready classes hclasses)
      (htableBound classes hclasses) hmembers' hcount

end Ix.Compile.Verify
