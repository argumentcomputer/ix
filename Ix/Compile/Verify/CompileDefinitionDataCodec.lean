import Ix.Compile.Verify.CompileDefinitionCodec

/-!
# Common definition-like production driver

The source `Def` representation covers definitions, theorems, and opaque
declarations.  This layer verifies their shared two-expression compiler once;
the singleton theorem and opaque dispatches are thin specializations below.
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

private theorem run_withMutCtx (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (mutCtx : Ix.MutCtx) (action : Ix.CompileM.CompileM α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.withMutCtx mutCtx action) =
      Ix.CompileM.CompileM.run compileEnv
        { blockEnv with mutCtx := mutCtx } state action := by
  rfl

def compiledDefinitionDataPayload (definitionData : Ix.Def)
    (typeExpr valueExpr : Ixon.Expr) : Ixon.Definition :=
  { kind := definitionData.kind
    safety := definitionData.safety
    lvls := definitionData.levelParams.size.toUInt64
    typ := typeExpr
    value := valueExpr }

def definitionDataHints (definitionData : Ix.Def) :
    Lean.ReducibilityHints :=
  match definitionData.kind with
  | .defn => definitionData.hints
  | .thm | .opaq => .opaque

private def definitionDataMutNames (blockEnv : Ix.CompileM.BlockEnv) :
    Array Ix.Name :=
  blockEnv.mutCtx.toList.toArray.map (·.1)

private def definitionDataMutCtxAddrs (blockEnv : Ix.CompileM.BlockEnv) :
    Array Address :=
  blockEnv.mutCtx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map
      (·.1.getHash)

/-- The common definition-like metadata finalizer is total and preserves the
primary reference/universe tables. -/
theorem finishDefinitionDataCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionData : Ix.Def)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishDefinitionDataCompilation definitionData
            typeExpr typeRoot valueExpr valueRoot) =
        .ok ((compiledDefinitionDataPayload definitionData typeExpr valueExpr,
          constMeta, typeExpr, valueExpr), state') ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = {} ∧
      state'.canonUnivCache = state.canonUnivCache := by
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
  let afterName := afterCache.compileName definitionData.name
  let afterLevels := afterName.compileNames definitionData.levelParams
  let afterAll := afterLevels.compileNames definitionData.all
  let mutNames := definitionDataMutNames blockEnv
  let afterMut := afterAll.compileNames mutNames
  let state' : Ix.CompileM.BlockState :=
    { afterMut with defHints :=
        afterMut.defHints.insert definitionData.name
          <| definitionDataHints definitionData }
  let ctxAddrs := definitionDataMutCtxAddrs blockEnv
  let constMeta := { Ixon.ConstantMeta.new
      (.defn definitionData.name.getHash
        (definitionData.levelParams.map (·.getHash))
        (definitionData.all.map (·.getHash)) ctxAddrs state.arena
        typeRoot valueRoot) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  have hname := MetaStateFrame.compileName afterCache definitionData.name
  have hlevels := MetaStateFrame.compileNames afterName
    definitionData.levelParams
  have hall := MetaStateFrame.compileNames afterLevels definitionData.all
  have hmut := MetaStateFrame.compileNames afterAll mutNames
  have hhints : MetaStateFrame afterMut state' :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hframe := hname.trans <| hlevels.trans <| hall.trans <|
    hmut.trans hhints
  refine ⟨constMeta, state', ?_, ?_, ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterMut := rfl
      _ = exprTableView afterAll :=
        BlockState.compileNames_exprTableView afterAll mutNames
      _ = exprTableView afterLevels :=
        BlockState.compileNames_exprTableView afterLevels definitionData.all
      _ = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          definitionData.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache definitionData.name).tables
      _ = exprTableView state := rfl
  · exact hframe.exprCache
  · exact hframe.canonUnivCache

def definitionDataCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (definitionData : Ix.Def) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := definitionData.name
    univCtx := definitionData.levelParams.toList }

theorem compileDefinitionData_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionData : Ix.Def) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileDefinitionData definitionData) =
      Ix.CompileM.CompileM.run compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData)
        (definitionCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr definitionData.type
          let (valueExpr, valueRoot) ←
            Ix.CompileM.compileExpr definitionData.value
          Ix.CompileM.finishDefinitionDataCompilation definitionData
            typeExpr typeRoot valueExpr valueRoot) := by
  rfl

theorem compileDefinitionData_run_of_compileExprs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (definitionData : Ix.Def)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeState : Ix.CompileM.BlockState)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64)
    (valueState : Ix.CompileM.BlockState)
    (htype : Ix.CompileM.CompileM.run compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData)
      (definitionCompileStartState state)
      (Ix.CompileM.compileExpr definitionData.type) =
        .ok ((typeExpr, typeRoot), typeState))
    (hvalue : Ix.CompileM.CompileM.run compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) typeState
      (Ix.CompileM.compileExpr definitionData.value) =
        .ok ((valueExpr, valueRoot), valueState)) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionData definitionData) =
        .ok ((compiledDefinitionDataPayload definitionData typeExpr valueExpr,
          constMeta, typeExpr, valueExpr), state') ∧
      exprTableView state' = exprTableView valueState ∧
      state'.exprCache = {} ∧
      state'.canonUnivCache = valueState.canonUnivCache := by
  obtain ⟨constMeta, state', hfinish, htables, hexprCache, hcanonCache⟩ :=
    finishDefinitionDataCompilation_run compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) valueState
      definitionData typeExpr typeRoot valueExpr valueRoot
  refine ⟨constMeta, state', ?_, htables, hexprCache, hcanonCache⟩
  rw [compileDefinitionData_run_eq, run_bind, htype]
  simp only
  rw [run_bind, hvalue]
  exact hfinish

/-- Sequential ordinary compilation of any `Def` produces its exact
reference-compiled payload and preserves wire-safe primary tables. -/
theorem compileDefinitionData_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionData : Ix.Def)
    {state : Ix.CompileM.BlockState} {typeTarget valueTarget : Ixon.Expr}
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionData.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionData.value)
    (htypeBound : ExprWireBound definitionData.type)
    (hvalueBound : ExprWireBound definitionData.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
      snapshot (definitionCompileStartState state))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.value = some valueTarget) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionData definitionData) =
        .ok ((compiledDefinitionDataPayload definitionData
          typeTarget valueTarget, constMeta, typeTarget, valueTarget), state') ∧
      BlockWireTablesWF state' ∧
      exprTableView state' = exprTableView snapshot ∧
      (compiledDefinitionDataPayload definitionData
        typeTarget valueTarget).wireWF ∧
      state'.exprCache = {} ∧
      CanonUnivCacheWF state' := by
  obtain ⟨typeRoot, typeState, htypeRun, htypeState, htypeWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) snapshot hfree
      hclosed hlevelFaithful hexprFaithful htypeSource htypeBound hstate
      htypeRef
  obtain ⟨valueRoot, valueState, hvalueRun, hvalueState, hvalueWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) snapshot hfree
      hclosed hlevelFaithful hexprFaithful hvalueSource hvalueBound htypeState
      hvalueRef
  obtain ⟨constMeta, state', hrun, htablesFrame, hexprCache,
      hcanonCache⟩ :=
    compileDefinitionData_run_of_compileExprs compileEnv blockEnv state
      definitionData typeTarget typeRoot typeState valueTarget valueRoot
      valueState htypeRun hvalueRun
  have htableEq : exprTableView state' = exprTableView snapshot :=
    htablesFrame.trans hvalueState.tables
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq htableEq
  have hdefWire : (compiledDefinitionDataPayload definitionData
      typeTarget valueTarget).wireWF := ⟨htypeWire, hvalueWire⟩
  exact ⟨constMeta, state', hrun, htables', htableEq, hdefWire,
    hexprCache, hvalueState.canonUnivCache.of_cache_eq hcanonCache⟩

/-- Common definition-like payload compilation followed by canonical sharing
returns an exactly decodable block. -/
theorem compileDefinitionDataBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionData : Ix.Def)
    {state : Ix.CompileM.BlockState} {typeTarget valueTarget : Ixon.Expr}
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionData.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionData.value)
    (htypeBound : ExprWireBound definitionData.type)
    (hvalueBound : ExprWireBound definitionData.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
      snapshot (definitionCompileStartState state))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.value = some valueTarget) :
    ∃ constMeta state',
      let info : Ixon.ConstantInfo :=
        .defn (compiledDefinitionDataPayload definitionData
          typeTarget valueTarget)
      let result := Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state'.refs state'.univs)
        constMeta
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionDataBlock definitionData) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hdefinition, htables', _, hinfo, _, _⟩ :=
    compileDefinitionData_run_ordinary_wireWF compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables definitionData
      htypeSource hvalueSource htypeBound hvalueBound hstate htypeRef
      hvalueRef
  have hfinish := finishConstantInfoWithSharing_run_codecWF
    compileEnv blockEnv state'
    (.defn (compiledDefinitionDataPayload definitionData
      typeTarget valueTarget)) constMeta hinfo htables'
  refine ⟨constMeta, state', ?_⟩
  dsimp only
  dsimp only at hfinish
  unfold Ix.CompileM.compileDefinitionDataBlock
  rw [run_bind, hdefinition]
  exact hfinish

/-- A successful two-root preseed followed by the common definition-like
block inherits the complete codec postcondition. -/
theorem compileDefinitionDataInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (definitionData : Ix.Def)
    (state preseedState : Ix.CompileM.BlockState)
    {typeTarget valueTarget : Ixon.Expr}
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        #[(definitionData.type, definitionData.levelParams.toList),
          (definitionData.value, definitionData.levelParams.toList)]) =
        .ok ((), preseedState))
    (htypeSource : SupportedOrdinaryExpr levelSupport definitionData.type)
    (hvalueSource : SupportedOrdinaryExpr levelSupport definitionData.value)
    (htypeBound : ExprWireBound definitionData.type)
    (hvalueBound : ExprWireBound definitionData.value)
    (hstate : FrozenExprStateWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
      snapshot (definitionCompileStartState preseedState))
    (htypeRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.type = some typeTarget)
    (hvalueRef : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) snapshot)
      definitionData.value = some valueTarget) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionDataInfo definitionData) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hrun, hcodec⟩ :=
    compileDefinitionDataBlock_run_ordinary_codecWF compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      definitionData htypeSource hvalueSource htypeBound hvalueBound hstate
      htypeRef hvalueRef
  let info : Ixon.ConstantInfo :=
    .defn (compiledDefinitionDataPayload definitionData
      typeTarget valueTarget)
  let result := Ix.CompileM.BlockResult.mk'
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state'.refs state'.univs)
    constMeta
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileDefinitionDataInfo
  rw [run_bind, hpreseed]
  exact hrun

/-- Source readiness constructs the shared two-root preseed and the complete
definition-like block codec postcondition. -/
theorem compileDefinitionDataInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (definitionData : Ix.Def) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv definitionData.levelParams.toList)
      levelSupport (preseedContextStartState state) definitionData.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv definitionData.levelParams.toList)
      levelSupport (preseedContextStartState state) definitionData.value)
    (htableBound : PairPreseedSourceBound blockEnv state
      definitionData.type definitionData.value)
    (htypeBound : ExprWireBound definitionData.type)
    (hvalueBound : ExprWireBound definitionData.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDefinitionDataInfo definitionData) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let params := definitionData.levelParams.toList
  obtain ⟨preseedState, typeTarget, valueTarget, hpreseed, htables,
      htypeRef, hvalueRef, hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_pair_run_ready_frozenRefs compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful htypeReady hvalueReady
      hcanonCache hrefTable hunivTable htableBound
  have hexprPreseed : preseedState.exprCache = {} :=
    hexpr.trans hexprCache
  have hfrozen : FrozenExprStateWF compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
      preseedState (definitionCompileStartState preseedState) :=
    definitionCompileStartState_frozen compileEnv
      (definitionDataCompileBlockEnv blockEnv definitionData) levelSupport
      preseedState hexprPreseed hcanonState
  have htypeRef' : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) preseedState)
      definitionData.type = some typeTarget := by
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      definitionDataCompileBlockEnv] using htypeRef
  have hvalueRef' : compileExprRef
      (frozenRefCompileCtx compileEnv
        (definitionDataCompileBlockEnv blockEnv definitionData) preseedState)
      definitionData.value = some valueTarget := by
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      definitionDataCompileBlockEnv] using hvalueRef
  exact compileDefinitionDataInfo_run_ordinary_codecWF compileEnv blockEnv
    preseedState hfree hclosed hlevelFaithful hexprFaithful htables
    definitionData state preseedState hpreseed htypeReady.supported
    hvalueReady.supported htypeBound hvalueBound hfrozen htypeRef' hvalueRef'

def singletonDefinitionDataBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (definitionData : Ix.Def) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert definitionData.name 0 }

private theorem auditTwoExprs_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (owner : Ix.Name) (typeSource valueSource : Ix.Expr)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (do
      Ix.CompileM.auditPlanHeadArities owner typeSource
      Ix.CompileM.auditPlanHeadArities owner valueSource) =
        .ok ((), state) := by
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree _ _ _ _ _ hfree]
  exact auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
    owner valueSource hfree

theorem auditConstantInfoPlanHeads_theorem_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (theoremVal : Ix.TheoremVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.thmInfo theoremVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities theoremVal.cnst.name
      theoremVal.cnst.type
    Ix.CompileM.auditPlanHeadArities theoremVal.cnst.name
      theoremVal.value) = .ok ((), state)
  exact auditTwoExprs_run_surgeryFree compileEnv blockEnv state
    theoremVal.cnst.name theoremVal.cnst.type theoremVal.value hfree

theorem compileConstantInfo_theorem_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (theoremVal : Ix.TheoremVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.thmInfo theoremVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.theoremValData theoremVal)) state
        (Ix.CompileM.compileTheoremInfo theoremVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.thmInfo theoremVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert theoremVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileTheoremInfo theoremVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_theorem_run_surgeryFree
      compileEnv blockEnv state theoremVal hfree]
  simpa only [singletonDefinitionDataBlockEnv,
    Ix.CompileM.theoremValData] using
      run_withMutCtx compileEnv blockEnv state
        ((Std.TreeMap.empty : Ix.MutCtx).insert theoremVal.cnst.name 0)
        (Ix.CompileM.compileTheoremInfo theoremVal)

/-- The actual singleton theorem dispatch derives its two-root preseed and
ends in a codec-safe block. -/
theorem compileConstantInfo_theorem_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (theoremVal : Ix.TheoremVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.theoremValData theoremVal))
        theoremVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state) theoremVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.theoremValData theoremVal))
        theoremVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state) theoremVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionDataBlockEnv blockEnv
        (Ix.CompileM.theoremValData theoremVal)) state
      theoremVal.cnst.type theoremVal.value)
    (htypeBound : ExprWireBound theoremVal.cnst.type)
    (hvalueBound : ExprWireBound theoremVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.thmInfo theoremVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let definitionData := Ix.CompileM.theoremValData theoremVal
  let singletonEnv :=
    singletonDefinitionDataBlockEnv blockEnv definitionData
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileDefinitionDataInfo_run_ready_codecWF compileEnv singletonEnv
      hfree hclosed hlevelFaithful hexprFaithful definitionData state
      hexprCache hcanonCache hrefTable hunivTable htypeReady hvalueReady
      htableBound htypeBound hvalueBound
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_theorem_run_surgeryFree_eq
    compileEnv blockEnv state theoremVal hfree]
  exact hrun

theorem compileConstantInfo_theorem_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (theoremVal : Ix.TheoremVal)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.theoremValData theoremVal))
        theoremVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      theoremVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.theoremValData theoremVal))
        theoremVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      theoremVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionDataBlockEnv blockEnv
        (Ix.CompileM.theoremValData theoremVal))
      (default : Ix.CompileM.BlockState)
      theoremVal.cnst.type theoremVal.value)
    (htypeBound : ExprWireBound theoremVal.cnst.type)
    (hvalueBound : ExprWireBound theoremVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.thmInfo theoremVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_theorem_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful theoremVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty htypeReady hvalueReady
    htableBound htypeBound hvalueBound

theorem auditConstantInfoPlanHeads_opaque_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (opaqueVal : Ix.OpaqueVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.opaqueInfo opaqueVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities opaqueVal.cnst.name
      opaqueVal.cnst.type
    Ix.CompileM.auditPlanHeadArities opaqueVal.cnst.name opaqueVal.value) =
      .ok ((), state)
  exact auditTwoExprs_run_surgeryFree compileEnv blockEnv state
    opaqueVal.cnst.name opaqueVal.cnst.type opaqueVal.value hfree

theorem compileConstantInfo_opaque_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (opaqueVal : Ix.OpaqueVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.opaqueInfo opaqueVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.opaqueValData opaqueVal)) state
        (Ix.CompileM.compileOpaqueInfo opaqueVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.opaqueInfo opaqueVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert opaqueVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileOpaqueInfo opaqueVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_opaque_run_surgeryFree
      compileEnv blockEnv state opaqueVal hfree]
  simpa only [singletonDefinitionDataBlockEnv,
    Ix.CompileM.opaqueValData] using
      run_withMutCtx compileEnv blockEnv state
        ((Std.TreeMap.empty : Ix.MutCtx).insert opaqueVal.cnst.name 0)
        (Ix.CompileM.compileOpaqueInfo opaqueVal)

/-- The actual singleton opaque dispatch derives its two-root preseed and
ends in a codec-safe block. -/
theorem compileConstantInfo_opaque_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (opaqueVal : Ix.OpaqueVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.opaqueValData opaqueVal))
        opaqueVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state) opaqueVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.opaqueValData opaqueVal))
        opaqueVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state) opaqueVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionDataBlockEnv blockEnv
        (Ix.CompileM.opaqueValData opaqueVal)) state
      opaqueVal.cnst.type opaqueVal.value)
    (htypeBound : ExprWireBound opaqueVal.cnst.type)
    (hvalueBound : ExprWireBound opaqueVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.opaqueInfo opaqueVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let definitionData := Ix.CompileM.opaqueValData opaqueVal
  let singletonEnv :=
    singletonDefinitionDataBlockEnv blockEnv definitionData
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileDefinitionDataInfo_run_ready_codecWF compileEnv singletonEnv
      hfree hclosed hlevelFaithful hexprFaithful definitionData state
      hexprCache hcanonCache hrefTable hunivTable htypeReady hvalueReady
      htableBound htypeBound hvalueBound
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_opaque_run_surgeryFree_eq
    compileEnv blockEnv state opaqueVal hfree]
  exact hrun

theorem compileConstantInfo_opaque_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (opaqueVal : Ix.OpaqueVal)
    (htypeReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.opaqueValData opaqueVal))
        opaqueVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      opaqueVal.cnst.type)
    (hvalueReady : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonDefinitionDataBlockEnv blockEnv
          (Ix.CompileM.opaqueValData opaqueVal))
        opaqueVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      opaqueVal.value)
    (htableBound : PairPreseedSourceBound
      (singletonDefinitionDataBlockEnv blockEnv
        (Ix.CompileM.opaqueValData opaqueVal))
      (default : Ix.CompileM.BlockState)
      opaqueVal.cnst.type opaqueVal.value)
    (htypeBound : ExprWireBound opaqueVal.cnst.type)
    (hvalueBound : ExprWireBound opaqueVal.value) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.opaqueInfo opaqueVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_opaque_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful opaqueVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty htypeReady hvalueReady
    htableBound htypeBound hvalueBound

end Ix.Compile.Verify
