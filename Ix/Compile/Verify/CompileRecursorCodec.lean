import Ix.Compile.Verify.CompileQuotientCodec

/-!
# Production recursor-driver/codec bridge

Standalone recursors preseed a nonempty source list consisting of their type
and every rule RHS.  This module verifies the production rule fold, metadata
finalizer, singleton driver, and resulting serialized block.
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

def compiledRecursorRule (rule : Ix.RecursorRule)
    (rhs : Ixon.Expr) : Ixon.RecursorRule :=
  { fields := rule.nfields.toUInt64, rhs }

def compiledRecursorPayload (recursorVal : Ix.RecursorVal)
    (typeExpr : Ixon.Expr) (rules : Array Ixon.RecursorRule) :
    Ixon.Recursor :=
  { k := recursorVal.k
    isUnsafe := recursorVal.isUnsafe
    lvls := recursorVal.cnst.levelParams.size.toUInt64
    params := recursorVal.numParams.toUInt64
    indices := recursorVal.numIndices.toUInt64
    motives := recursorVal.numMotives.toUInt64
    minors := recursorVal.numMinors.toUInt64
    typ := typeExpr
    rules }

/-- A production rule fold preserves the frozen expression state, appends
exactly one wire-safe rule per source rule, and retains source order. -/
theorem compileRecursorRules_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (sourceRules : List Ix.RecursorRule)
    (acc : Ix.CompileM.RecursorRuleCompileState)
    {state : Ix.CompileM.BlockState}
    (hsources : ∀ rule ∈ sourceRules,
      SupportedOrdinaryExpr levelSupport rule.rhs)
    (hbounds : ∀ rule ∈ sourceRules, ExprWireBound rule.rhs)
    (hrefs : ∀ rule ∈ sourceRules, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv blockEnv snapshot) rule.rhs =
          some target)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state)
    (hacc : ∀ rule ∈ acc.rules, rule.wireWF) :
    ∃ finalAcc state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursorRules sourceRules acc) =
        .ok (finalAcc, state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      finalAcc.rules.size = acc.rules.size + sourceRules.length ∧
      (∀ rule ∈ finalAcc.rules, rule.wireWF) := by
  induction sourceRules generalizing acc state with
  | nil =>
      exact ⟨acc, state, run_pure compileEnv blockEnv state acc,
        hstate, by simp, hacc⟩
  | cons source rest ih =>
      have hsource : SupportedOrdinaryExpr levelSupport source.rhs :=
        hsources source (by simp)
      have hbound : ExprWireBound source.rhs :=
        hbounds source (by simp)
      obtain ⟨target, href⟩ := hrefs source (by simp)
      obtain ⟨root, nextState, hcompile, hnext, htarget⟩ :=
        compileExpr_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
          hclosed hlevelFaithful hexprFaithful hsource hbound hstate href
      let compiledRule := compiledRecursorRule source target
      let nextAcc : Ix.CompileM.RecursorRuleCompileState := {
        rules := acc.rules.push compiledRule
        ruleAddrs := acc.ruleAddrs.push source.ctor.getHash
        ruleRoots := acc.ruleRoots.push root }
      have hnextAcc : ∀ rule ∈ nextAcc.rules, rule.wireWF := by
        intro rule hmem
        simp only [nextAcc, Array.mem_push] at hmem
        rcases hmem with hmem | rfl
        · exact hacc rule hmem
        · exact htarget
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState,
          hsize, hfinalRules⟩ :=
        ih nextAcc (fun rule hmem => hsources rule (by simp [hmem]))
          (fun rule hmem => hbounds rule (by simp [hmem]))
          (fun rule hmem => hrefs rule (by simp [hmem])) hnext hnextAcc
      refine ⟨finalAcc, finalState, ?_, hfinalState, ?_, hfinalRules⟩
      · unfold Ix.CompileM.compileRecursorRules
        rw [run_bind]
        unfold Ix.CompileM.compileRecursorRule
        rw [run_bind, hcompile]
        simp only
        exact hrestRun
      · dsimp only [nextAcc] at hsize
        simp only [Array.size_push] at hsize
        simp only [List.length_cons]
        omega

private def recursorMutNames (blockEnv : Ix.CompileM.BlockEnv) :
    Array Ix.Name :=
  blockEnv.mutCtx.toList.toArray.map (·.1)

private def recursorMutCtxAddrs (blockEnv : Ix.CompileM.BlockEnv) :
    Array Address :=
  blockEnv.mutCtx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map
      (·.1.getHash)

/-- The recursor metadata finalizer is total and preserves the primary
reference/universe tables. -/
theorem finishRecursorCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (recursorVal : Ix.RecursorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (compiledRules : Ix.CompileM.RecursorRuleCompileState) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishRecursorCompilation recursorVal typeExpr
            typeRoot compiledRules) =
        .ok ((compiledRecursorPayload recursorVal typeExpr
          compiledRules.rules, constMeta, typeExpr), state') ∧
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
  let afterName := afterCache.compileName recursorVal.cnst.name
  let afterLevels := afterName.compileNames recursorVal.cnst.levelParams
  let afterAll := afterLevels.compileNames recursorVal.all
  let mutNames := recursorMutNames blockEnv
  let afterMut := afterAll.compileNames mutNames
  let ruleNames := recursorVal.rules.map (·.ctor)
  let state' := afterMut.compileNames ruleNames
  let ctxAddrs := recursorMutCtxAddrs blockEnv
  let constMeta := { Ixon.ConstantMeta.new
      (.recr recursorVal.cnst.name.getHash
        (recursorVal.cnst.levelParams.map (·.getHash))
        compiledRules.ruleAddrs (recursorVal.all.map (·.getHash))
        ctxAddrs state.arena typeRoot compiledRules.ruleRoots) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  have hname := MetaStateFrame.compileName afterCache recursorVal.cnst.name
  have hlevels := MetaStateFrame.compileNames afterName
    recursorVal.cnst.levelParams
  have hall := MetaStateFrame.compileNames afterLevels recursorVal.all
  have hmut := MetaStateFrame.compileNames afterAll mutNames
  have hrules := MetaStateFrame.compileNames afterMut ruleNames
  have hframe := hname.trans <| hlevels.trans <| hall.trans <|
    hmut.trans hrules
  refine ⟨constMeta, state', ?_, ?_, ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterMut :=
        BlockState.compileNames_exprTableView afterMut ruleNames
      _ = exprTableView afterAll :=
        BlockState.compileNames_exprTableView afterAll mutNames
      _ = exprTableView afterLevels :=
        BlockState.compileNames_exprTableView afterLevels recursorVal.all
      _ = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          recursorVal.cnst.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache recursorVal.cnst.name).tables
      _ = exprTableView state := rfl
  · exact hframe.exprCache
  · exact hframe.canonUnivCache

def recursorCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (recursorVal : Ix.RecursorVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := recursorVal.cnst.name
    univCtx := recursorVal.cnst.levelParams.toList }

theorem compileRecursor_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (recursorVal : Ix.RecursorVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileRecursor recursorVal) =
      Ix.CompileM.CompileM.run compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal)
        (axiomCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr recursorVal.cnst.type
          let compiledRules ← Ix.CompileM.compileRecursorRules
            recursorVal.rules.toList {}
          Ix.CompileM.finishRecursorCompilation recursorVal
            typeExpr typeRoot compiledRules) := by
  rfl

/-- Sequential ordinary compilation of a recursor produces a wire-safe
payload and preserves wire-safe primary tables. -/
theorem compileRecursor_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (recursorVal : Ix.RecursorVal)
    {state : Ix.CompileM.BlockState}
    (htypeSource : SupportedOrdinaryExpr levelSupport recursorVal.cnst.type)
    (hruleSources : ∀ rule ∈ recursorVal.rules.toList,
      SupportedOrdinaryExpr levelSupport rule.rhs)
    (htypeBound : ExprWireBound recursorVal.cnst.type)
    (hruleBounds : ∀ rule ∈ recursorVal.rules.toList,
      ExprWireBound rule.rhs)
    (hruleCount : recursorVal.rules.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) levelSupport snapshot
      (axiomCompileStartState state))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
      recursorVal.cnst.type = some typeTarget)
    (hruleRefs : ∀ rule ∈ recursorVal.rules.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
        rule.rhs = some target) :
    ∃ recursor constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursor recursorVal) =
        .ok ((recursor, constMeta, recursor.typ), state') ∧
      BlockWireTablesWF state' ∧
      exprTableView state' = exprTableView snapshot ∧
      recursor.wireWF ∧
      state'.exprCache = {} ∧
      CanonUnivCacheWF state' := by
  obtain ⟨typeTarget, htypeRef⟩ := htypeRef
  obtain ⟨typeRoot, typeState, htypeRun, htypeState, htypeWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful htypeSource htypeBound hstate htypeRef
  obtain ⟨compiledRules, ruleState, hrulesRun, hrulesState,
      hrulesSize, hrulesWire⟩ :=
    compileRecursorRules_run_ordinary_wireWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful recursorVal.rules.toList
      ({} : Ix.CompileM.RecursorRuleCompileState) hruleSources hruleBounds
      hruleRefs htypeState (by simp)
  obtain ⟨constMeta, state', hfinish, htablesFrame, hexprCache,
      hcanonCache⟩ :=
    finishRecursorCompilation_run compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) ruleState recursorVal
      typeTarget typeRoot compiledRules
  let recursor := compiledRecursorPayload recursorVal typeTarget
    compiledRules.rules
  have hcompiledSize : compiledRules.rules.size = recursorVal.rules.size := by
    simpa using hrulesSize
  have hwire : recursor.wireWF := by
    refine ⟨htypeWire, ?_, ?_⟩
    · simpa [recursor, compiledRecursorPayload, hcompiledSize] using hruleCount
    · intro rule hmem
      exact hrulesWire rule hmem
  have htableEq : exprTableView state' = exprTableView snapshot :=
    htablesFrame.trans hrulesState.tables
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq htableEq
  refine ⟨recursor, constMeta, state', ?_, htables', htableEq, hwire, hexprCache,
    hrulesState.canonUnivCache.of_cache_eq hcanonCache⟩
  rw [compileRecursor_run_eq, run_bind, htypeRun]
  simp only
  rw [run_bind, hrulesRun]
  exact hfinish

theorem compileRecursorBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (recursorVal : Ix.RecursorVal)
    {state : Ix.CompileM.BlockState}
    (htypeSource : SupportedOrdinaryExpr levelSupport recursorVal.cnst.type)
    (hruleSources : ∀ rule ∈ recursorVal.rules.toList,
      SupportedOrdinaryExpr levelSupport rule.rhs)
    (htypeBound : ExprWireBound recursorVal.cnst.type)
    (hruleBounds : ∀ rule ∈ recursorVal.rules.toList,
      ExprWireBound rule.rhs)
    (hruleCount : recursorVal.rules.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) levelSupport snapshot
      (axiomCompileStartState state))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
      recursorVal.cnst.type = some typeTarget)
    (hruleRefs : ∀ rule ∈ recursorVal.rules.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
        rule.rhs = some target) :
    ∃ recursor constMeta state',
      let info : Ixon.ConstantInfo := .recr recursor
      let result := Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state'.refs state'.univs)
        constMeta
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursorBlock recursorVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨recursor, constMeta, state', hrecursor, htables', _, hwire,
      _, _⟩ :=
    compileRecursor_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables recursorVal htypeSource
      hruleSources htypeBound hruleBounds hruleCount hstate htypeRef
      hruleRefs
  have hfinish := finishConstantInfoWithSharing_run_codecWF
    compileEnv blockEnv state' (.recr recursor) constMeta hwire htables'
  refine ⟨recursor, constMeta, state', ?_⟩
  dsimp only
  dsimp only at hfinish
  unfold Ix.CompileM.compileRecursorBlock
  rw [run_bind, hrecursor]
  exact hfinish

theorem compileRecursorInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (recursorVal : Ix.RecursorVal)
    (state preseedState : Ix.CompileM.BlockState)
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.recursorPreseedExprs recursorVal)) =
        .ok ((), preseedState))
    (htypeSource : SupportedOrdinaryExpr levelSupport recursorVal.cnst.type)
    (hruleSources : ∀ rule ∈ recursorVal.rules.toList,
      SupportedOrdinaryExpr levelSupport rule.rhs)
    (htypeBound : ExprWireBound recursorVal.cnst.type)
    (hruleBounds : ∀ rule ∈ recursorVal.rules.toList,
      ExprWireBound rule.rhs)
    (hruleCount : recursorVal.rules.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) levelSupport snapshot
      (axiomCompileStartState preseedState))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
      recursorVal.cnst.type = some typeTarget)
    (hruleRefs : ∀ rule ∈ recursorVal.rules.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (recursorCompileBlockEnv blockEnv recursorVal) snapshot)
        rule.rhs = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursorInfo recursorVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨recursor, constMeta, state', hrun, hcodec⟩ :=
    compileRecursorBlock_run_ordinary_codecWF compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables recursorVal
      htypeSource hruleSources htypeBound hruleBounds hruleCount hstate
      htypeRef hruleRefs
  let info : Ixon.ConstantInfo := .recr recursor
  let result := Ix.CompileM.BlockResult.mk'
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state'.refs state'.univs)
    constMeta
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileRecursorInfo
  rw [run_bind, hpreseed]
  exact hrun

def singletonRecursorBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (recursorVal : Ix.RecursorVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert recursorVal.cnst.name 0 }

/-- Source readiness constructs the recursor's nonempty root preseed, all
frozen RHS targets, and the final codec-safe singleton block. -/
theorem compileRecursorInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (recursorVal : Ix.RecursorVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hready : ∀ source ∈ Ix.CompileM.recursorSourceExprs recursorVal,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv
          recursorVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound blockEnv state
      (Ix.CompileM.recursorSourceExprs recursorVal))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.recursorSourceExprs recursorVal, ExprWireBound source)
    (hruleCount : recursorVal.rules.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileRecursorInfo recursorVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let params := recursorVal.cnst.levelParams.toList
  let rest := recursorVal.rules.toList.map (·.rhs)
  have htypeMem : recursorVal.cnst.type ∈
      Ix.CompileM.recursorSourceExprs recursorVal := by
    simp [Ix.CompileM.recursorSourceExprs]
  have hruleMem : ∀ rule ∈ recursorVal.rules.toList,
      rule.rhs ∈ Ix.CompileM.recursorSourceExprs recursorVal := by
    intro rule hmem
    unfold Ix.CompileM.recursorSourceExprs
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨rule, hmem, rfl⟩)
  have hrestReady : ∀ source ∈ rest,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) source := by
    intro source hmem
    apply hready source
    simp only [Ix.CompileM.recursorSourceExprs]
    exact List.mem_cons_of_mem _ hmem
  obtain ⟨preseedState, hpreseed, htables, htargets, hexpr,
      hcanonState, harena, hfinal⟩ :=
    preseedExprTables_roots_run_ready_frozenRefs compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful recursorVal.cnst.type rest
      (hready _ htypeMem) hrestReady hcanonCache hrefTable hunivTable
      htableBound
  have hpreseed' : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.recursorPreseedExprs recursorVal)) =
        .ok ((), preseedState) := by
    simpa [Ix.CompileM.recursorPreseedExprs,
      Ix.CompileM.recursorSourceExprs, rest] using hpreseed
  have hexprPreseed : preseedState.exprCache = {} :=
    hexpr.trans hexprCache
  have hfrozen : FrozenExprStateWF compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) levelSupport
      preseedState (axiomCompileStartState preseedState) :=
    axiomCompileStartState_frozen compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) levelSupport
      preseedState hexprPreseed hcanonState
  have htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
      (recursorCompileBlockEnv blockEnv recursorVal) preseedState)
      recursorVal.cnst.type = some typeTarget := by
    obtain ⟨target, href⟩ := htargets recursorVal.cnst.type
      (List.mem_cons_self)
    refine ⟨target, ?_⟩
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      recursorCompileBlockEnv] using href
  have hruleRefs : ∀ rule ∈ recursorVal.rules.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
        (recursorCompileBlockEnv blockEnv recursorVal) preseedState)
        rule.rhs = some target := by
    intro rule hmem
    have hrhsRest : rule.rhs ∈ rest := by
      exact List.mem_map.mpr ⟨rule, hmem, rfl⟩
    obtain ⟨target, href⟩ := htargets rule.rhs
      (List.mem_cons_of_mem _ hrhsRest)
    refine ⟨target, ?_⟩
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      recursorCompileBlockEnv] using href
  have htypeSource :
      SupportedOrdinaryExpr levelSupport recursorVal.cnst.type :=
    (hready _ htypeMem).supported
  have hruleSources : ∀ rule ∈ recursorVal.rules.toList,
      SupportedOrdinaryExpr levelSupport rule.rhs := by
    intro rule hmem
    exact (hready rule.rhs (hruleMem rule hmem)).supported
  have htypeBound : ExprWireBound recursorVal.cnst.type :=
    hexprBounds _ htypeMem
  have hruleBounds : ∀ rule ∈ recursorVal.rules.toList,
      ExprWireBound rule.rhs := by
    intro rule hmem
    exact hexprBounds rule.rhs (hruleMem rule hmem)
  exact compileRecursorInfo_run_ordinary_codecWF compileEnv blockEnv
    preseedState hfree hclosed hlevelFaithful hexprFaithful htables
    recursorVal state preseedState hpreseed' htypeSource hruleSources
    htypeBound hruleBounds hruleCount hfrozen htypeRef hruleRefs

theorem auditRecursorRulePlanHeads_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (owner : Ix.Name) (rules : List Ix.RecursorRule)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditRecursorRulePlanHeads owner rules) =
      .ok ((), state) := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      unfold Ix.CompileM.auditRecursorRulePlanHeads
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree
          compileEnv blockEnv state owner rule.rhs hfree]
      exact ih

theorem auditConstantInfoPlanHeads_recursor_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (recursorVal : Ix.RecursorVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.recInfo recursorVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities recursorVal.cnst.name
      recursorVal.cnst.type
    Ix.CompileM.auditRecursorRulePlanHeads recursorVal.cnst.name
      recursorVal.rules.toList) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
      recursorVal.cnst.name recursorVal.cnst.type hfree]
  exact auditRecursorRulePlanHeads_run_surgeryFree compileEnv blockEnv state
    recursorVal.cnst.name recursorVal.rules.toList hfree

theorem compileConstantInfo_recursor_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (recursorVal : Ix.RecursorVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.recInfo recursorVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonRecursorBlockEnv blockEnv recursorVal) state
        (Ix.CompileM.compileRecursorInfo recursorVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.recInfo recursorVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert recursorVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileRecursorInfo recursorVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_recursor_run_surgeryFree
      compileEnv blockEnv state recursorVal hfree]
  simpa only [singletonRecursorBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      ((Std.TreeMap.empty : Ix.MutCtx).insert recursorVal.cnst.name 0)
      (Ix.CompileM.compileRecursorInfo recursorVal)

/-- Actual standalone recursor dispatch from an arbitrary sound initial block
state.  The production root-list preseed discharges every frozen-reference
premise needed by the sequential rule fold. -/
theorem compileConstantInfo_recursor_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (recursorVal : Ix.RecursorVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hready : ∀ source ∈ Ix.CompileM.recursorSourceExprs recursorVal,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (singletonRecursorBlockEnv blockEnv recursorVal)
          recursorVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound
      (singletonRecursorBlockEnv blockEnv recursorVal) state
      (Ix.CompileM.recursorSourceExprs recursorVal))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.recursorSourceExprs recursorVal, ExprWireBound source)
    (hruleCount : recursorVal.rules.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.recInfo recursorVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonRecursorBlockEnv blockEnv recursorVal
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileRecursorInfo_run_ready_codecWF compileEnv singletonEnv hfree
      hclosed hlevelFaithful hexprFaithful recursorVal state hexprCache
      hcanonCache hrefTable hunivTable hready htableBound hexprBounds
      hruleCount
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_recursor_run_surgeryFree_eq
    compileEnv blockEnv state recursorVal hfree]
  exact hrun

/-- Driver-shaped specialization for the production default block state. -/
theorem compileConstantInfo_recursor_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (recursorVal : Ix.RecursorVal)
    (hready : ∀ source ∈ Ix.CompileM.recursorSourceExprs recursorVal,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (singletonRecursorBlockEnv blockEnv recursorVal)
          recursorVal.cnst.levelParams.toList)
        levelSupport
        (preseedContextStartState (default : Ix.CompileM.BlockState))
        source)
    (htableBound : RootPreseedSourceBound
      (singletonRecursorBlockEnv blockEnv recursorVal)
      (default : Ix.CompileM.BlockState)
      (Ix.CompileM.recursorSourceExprs recursorVal))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.recursorSourceExprs recursorVal, ExprWireBound source)
    (hruleCount : recursorVal.rules.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.recInfo recursorVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_recursor_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful recursorVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty hready htableBound
    hexprBounds hruleCount

end Ix.Compile.Verify
