import Ix.Compile.Verify.CompileAxiomCodec

/-!
# Production definition-driver/codec bridge

This layer verifies the two-expression singleton definition wrapper. It uses
the pair preseed theorem for the shared reference/universe tables, then
threads the frozen expression invariant from the type into the value before
the metadata and sharing finalizers.
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

private theorem run_withMutCtx (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (mutCtx : Ix.MutCtx) (action : Ix.CompileM.CompileM α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.withMutCtx mutCtx action) =
      Ix.CompileM.CompileM.run compileEnv
        { blockEnv with mutCtx := mutCtx } state action := by
  rfl

def compiledDefinitionPayload (definitionVal : Ix.DefinitionVal)
    (typeExpr valueExpr : Ixon.Expr) : Ixon.Definition :=
  { kind := .defn
    safety := Ix.CompileM.convertSafety definitionVal.safety
    lvls := definitionVal.cnst.levelParams.size.toUInt64
    typ := typeExpr
    value := valueExpr }

private def definitionMutNames (blockEnv : Ix.CompileM.BlockEnv) :
    Array Ix.Name :=
  blockEnv.mutCtx.toList.toArray.map (·.1)

private def definitionMutCtxAddrs (blockEnv : Ix.CompileM.BlockEnv) :
    Array Address :=
  blockEnv.mutCtx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map
      (·.1.getHash)

/-- The definition metadata finalizer is total and preserves the primary
reference/universe tables. -/
theorem finishDefinitionCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionVal : Ix.DefinitionVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishDefinitionCompilation definitionVal
            typeExpr typeRoot valueExpr valueRoot) =
        .ok ((compiledDefinitionPayload definitionVal typeExpr valueExpr,
          constMeta, typeExpr, valueExpr), state') ∧
      exprTableView state' = exprTableView state := by
  let afterArena : Ix.CompileM.BlockState :=
    { state with arena := {} }
  let afterSharing : Ix.CompileM.BlockState :=
    { afterArena with surgerySharing := #[] }
  let afterPatches : Ix.CompileM.BlockState :=
    { afterSharing with
      metaUnivs := #[]
      metaUnivsIndex := {}
      univPatches := #[] }
  let afterCache : Ix.CompileM.BlockState :=
    { afterPatches with exprCache := {} }
  let afterName := afterCache.compileName definitionVal.cnst.name
  let afterLevels := afterName.compileNames definitionVal.cnst.levelParams
  let afterAll := afterLevels.compileNames definitionVal.all
  let mutNames := definitionMutNames blockEnv
  let afterMut := afterAll.compileNames mutNames
  let state' : Ix.CompileM.BlockState :=
    { afterMut with defHints :=
        afterMut.defHints.insert definitionVal.cnst.name definitionVal.hints }
  let ctxAddrs := definitionMutCtxAddrs blockEnv
  let constMeta := { Ixon.ConstantMeta.new
      (.defn definitionVal.cnst.name.getHash
        (definitionVal.cnst.levelParams.map (·.getHash))
        (definitionVal.all.map (·.getHash)) ctxAddrs state.arena
        typeRoot valueRoot) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  refine ⟨constMeta, state', ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterMut := rfl
      _ = exprTableView afterAll :=
        BlockState.compileNames_exprTableView afterAll mutNames
      _ = exprTableView afterLevels :=
        BlockState.compileNames_exprTableView afterLevels definitionVal.all
      _ = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          definitionVal.cnst.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache definitionVal.cnst.name).tables
      _ = exprTableView state := rfl

def definitionCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (definitionVal : Ix.DefinitionVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := definitionVal.cnst.name
    univCtx := definitionVal.cnst.levelParams.toList }

def definitionCompileStartState (state : Ix.CompileM.BlockState) :
    Ix.CompileM.BlockState :=
  { state with
    univCache := {}
    arena := {}
    metaUnivs := #[]
    metaUnivsIndex := {}
    univPatches := #[] }

@[simp] theorem definitionCompileStartState_exprTableView
    (state : Ix.CompileM.BlockState) :
    exprTableView (definitionCompileStartState state) = exprTableView state := by
  rfl

theorem definitionCompileStartState_frozen
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (state : Ix.CompileM.BlockState)
    (hexpr : state.exprCache = {})
    (hcanon : CanonUnivCacheWF state) :
    FrozenExprStateWF compileEnv blockEnv levelSupport state
      (definitionCompileStartState state) := by
  refine
    { tables := definitionCompileStartState_exprTableView state
      exprCache := ?_
      univCache := ?_
      canonUnivCache := ?_ }
  · apply OrdinaryExprCacheWF.of_cache_eq
      (OrdinaryExprCacheWF.empty
        (frozenRefCompileCtx compileEnv blockEnv state))
    exact hexpr
  · apply UnivCacheWF.of_cache_eq
      (UnivCacheWF.empty (univParamIndex blockEnv.univCtx) levelSupport)
    rfl
  · exact hcanon.of_cache_eq rfl

theorem compileDefinition_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionVal : Ix.DefinitionVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileDefinition definitionVal) =
      Ix.CompileM.CompileM.run compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal)
        (definitionCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr definitionVal.cnst.type
          let (valueExpr, valueRoot) ←
            Ix.CompileM.compileExpr definitionVal.value
          Ix.CompileM.finishDefinitionCompilation definitionVal
            typeExpr typeRoot valueExpr valueRoot) := by
  rfl

theorem compileDefinition_run_of_compileExprs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionVal : Ix.DefinitionVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeState : Ix.CompileM.BlockState)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64)
    (valueState : Ix.CompileM.BlockState)
    (htype : Ix.CompileM.CompileM.run compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal)
      (definitionCompileStartState state)
      (Ix.CompileM.compileExpr definitionVal.cnst.type) =
        .ok ((typeExpr, typeRoot), typeState))
    (hvalue : Ix.CompileM.CompileM.run compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) typeState
      (Ix.CompileM.compileExpr definitionVal.value) =
        .ok ((valueExpr, valueRoot), valueState)) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinition definitionVal) =
        .ok ((compiledDefinitionPayload definitionVal typeExpr valueExpr,
          constMeta, typeExpr, valueExpr), state') ∧
      exprTableView state' = exprTableView valueState := by
  obtain ⟨constMeta, state', hfinish, htables⟩ :=
    finishDefinitionCompilation_run compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) valueState
      definitionVal typeExpr typeRoot valueExpr valueRoot
  refine ⟨constMeta, state', ?_, htables⟩
  rw [compileDefinition_run_eq, run_bind, htype]
  simp only
  rw [run_bind, hvalue]
  exact hfinish

/-- Sequential ordinary compilation produces the exact reference-compiled
type and value, a wire-safe definition payload, and wire-safe final tables. -/
theorem compileDefinition_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionVal : Ix.DefinitionVal)
    {state : Ix.CompileM.BlockState} {typeTarget valueTarget : Ixon.Expr}
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionVal.cnst.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) levelSupport snapshot
      (definitionCompileStartState state))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.cnst.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.value = some valueTarget) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinition definitionVal) =
        .ok ((compiledDefinitionPayload definitionVal typeTarget valueTarget,
          constMeta, typeTarget, valueTarget), state') ∧
      BlockWireTablesWF state' ∧
      (compiledDefinitionPayload definitionVal typeTarget valueTarget).wireWF := by
  obtain ⟨typeRoot, typeState, htypeRun, htypeState, htypeWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful htypeSource htypeBound hstate htypeRef
  obtain ⟨valueRoot, valueState, hvalueRun, hvalueState, hvalueWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful hvalueSource hvalueBound htypeState hvalueRef
  obtain ⟨constMeta, state', hrun, htablesFrame⟩ :=
    compileDefinition_run_of_compileExprs compileEnv blockEnv state
      definitionVal typeTarget typeRoot typeState valueTarget valueRoot
      valueState htypeRun hvalueRun
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq (htablesFrame.trans hvalueState.tables)
  exact ⟨constMeta, state', hrun, htables', htypeWire, hvalueWire⟩

/-- Definition payload compilation followed by canonical sharing and
`BlockResult` serialization returns an exactly decodable block. -/
theorem compileDefinitionBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionVal : Ix.DefinitionVal)
    {state : Ix.CompileM.BlockState} {typeTarget valueTarget : Ixon.Expr}
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionVal.cnst.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) levelSupport snapshot
      (definitionCompileStartState state))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.cnst.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.value = some valueTarget) :
    ∃ constMeta state',
      let info : Ixon.ConstantInfo :=
        .defn (compiledDefinitionPayload definitionVal typeTarget valueTarget)
      let result := Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state'.refs state'.univs)
        constMeta
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionBlock definitionVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hdefinition, htables', hinfo⟩ :=
    compileDefinition_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables definitionVal htypeSource
      hvalueSource htypeBound hvalueBound hstate htypeRef hvalueRef
  have hfinish := finishConstantInfoWithSharing_run_codecWF
    compileEnv blockEnv state'
    (.defn (compiledDefinitionPayload definitionVal typeTarget valueTarget))
    constMeta hinfo htables'
  refine ⟨constMeta, state', ?_⟩
  dsimp only
  dsimp only at hfinish
  unfold Ix.CompileM.compileDefinitionBlock
  rw [run_bind, hdefinition]
  exact hfinish

/-- A successful two-root preseed followed by the verified definition block
inherits the complete codec postcondition. -/
theorem compileDefinitionInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionVal : Ix.DefinitionVal)
    (state preseedState : Ix.CompileM.BlockState)
    {typeTarget valueTarget : Ixon.Expr}
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        #[(definitionVal.cnst.type,
            definitionVal.cnst.levelParams.toList),
          (definitionVal.value,
            definitionVal.cnst.levelParams.toList)]) =
        .ok ((), preseedState))
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionVal.cnst.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) levelSupport snapshot
      (definitionCompileStartState preseedState))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.cnst.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) snapshot)
      definitionVal.value = some valueTarget) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionInfo definitionVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hrun, hcodec⟩ :=
    compileDefinitionBlock_run_ordinary_codecWF compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables definitionVal
      htypeSource hvalueSource htypeBound hvalueBound hstate htypeRef hvalueRef
  let info : Ixon.ConstantInfo :=
    .defn (compiledDefinitionPayload definitionVal typeTarget valueTarget)
  let result := Ix.CompileM.BlockResult.mk'
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state'.refs state'.univs)
    constMeta
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileDefinitionInfo
  rw [run_bind, hpreseed]
  exact hrun

/-- Source readiness constructs the two-root preseed, both frozen reference
targets, the sequential frozen compiler state, and the final definition block
codec postcondition. -/
theorem compileDefinitionInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (definitionVal : Ix.DefinitionVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv
        definitionVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state)
      definitionVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv
        definitionVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state)
      definitionVal.value)
    (htableBound : PairPreseedSourceBound blockEnv state
      definitionVal.cnst.type definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionInfo definitionVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let params := definitionVal.cnst.levelParams.toList
  obtain ⟨preseedState, typeTarget, valueTarget, hpreseed, htables,
      htypeRef, hvalueRef, hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_pair_run_ready_frozenRefs compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful htypeReady hvalueReady
      hcanonCache hrefTable hunivTable htableBound
  have hexprPreseed : preseedState.exprCache = {} :=
    hexpr.trans hexprCache
  have hfrozen : FrozenExprStateWF compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) levelSupport
      preseedState (definitionCompileStartState preseedState) :=
    definitionCompileStartState_frozen compileEnv
      (definitionCompileBlockEnv blockEnv definitionVal) levelSupport
      preseedState hexprPreseed hcanonState
  have htypeRef' : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) preseedState)
      definitionVal.cnst.type = some typeTarget := by
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      definitionCompileBlockEnv] using htypeRef
  have hvalueRef' : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionCompileBlockEnv blockEnv definitionVal) preseedState)
      definitionVal.value = some valueTarget := by
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      definitionCompileBlockEnv] using hvalueRef
  exact compileDefinitionInfo_run_ordinary_codecWF compileEnv blockEnv
    preseedState hfree hclosed hlevelFaithful hexprFaithful htables
    definitionVal state preseedState hpreseed htypeReady.supported
    hvalueReady.supported htypeBound hvalueBound hfrozen htypeRef' hvalueRef'

def singletonDefinitionBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (definitionVal : Ix.DefinitionVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert definitionVal.cnst.name 0 }

theorem auditConstantInfoPlanHeads_definition_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionVal : Ix.DefinitionVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.defnInfo definitionVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities definitionVal.cnst.name
      definitionVal.cnst.type
    Ix.CompileM.auditPlanHeadArities definitionVal.cnst.name
      definitionVal.value) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree _ _ _ _ _ hfree]
  exact auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
    definitionVal.cnst.name definitionVal.value hfree

theorem compileConstantInfo_definition_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionVal : Ix.DefinitionVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.defnInfo definitionVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonDefinitionBlockEnv blockEnv definitionVal) state
        (Ix.CompileM.compileDefinitionInfo definitionVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.defnInfo definitionVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert definitionVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileDefinitionInfo definitionVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_definition_run_surgeryFree
      compileEnv blockEnv state definitionVal hfree]
  simpa only [singletonDefinitionBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      ((Std.TreeMap.empty : Ix.MutCtx).insert definitionVal.cnst.name 0)
      (Ix.CompileM.compileDefinitionInfo definitionVal)

/-- Actual singleton definition dispatch from an arbitrary sound initial
block state. No raw preseed execution, frozen-state, or coverage hypothesis is
required. -/
theorem compileConstantInfo_definition_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (definitionVal : Ix.DefinitionVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionBlockEnv blockEnv definitionVal)
        definitionVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state)
      definitionVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionBlockEnv blockEnv definitionVal)
        definitionVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state)
      definitionVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionBlockEnv blockEnv definitionVal) state
      definitionVal.cnst.type definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.defnInfo definitionVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonDefinitionBlockEnv blockEnv definitionVal
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileDefinitionInfo_run_ready_codecWF compileEnv singletonEnv hfree
      hclosed hlevelFaithful hexprFaithful definitionVal state hexprCache
      hcanonCache hrefTable hunivTable htypeReady hvalueReady htableBound
      htypeBound hvalueBound
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_definition_run_surgeryFree_eq
    compileEnv blockEnv state definitionVal hfree]
  exact hrun

/-- Driver-shaped specialization for the production default block state. -/
theorem compileConstantInfo_definition_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (definitionVal : Ix.DefinitionVal)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionBlockEnv blockEnv definitionVal)
        definitionVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      definitionVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionBlockEnv blockEnv definitionVal)
        definitionVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      definitionVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionBlockEnv blockEnv definitionVal)
      (default : Ix.CompileM.BlockState)
      definitionVal.cnst.type definitionVal.value)
    (htypeBound : ExprWireBound definitionVal.cnst.type)
    (hvalueBound : ExprWireBound definitionVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.defnInfo definitionVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_definition_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful definitionVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty htypeReady hvalueReady
    htableBound htypeBound hvalueBound

end Ix.Compile.Verify
