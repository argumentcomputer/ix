import Ix.Compile.Verify.CompileDefinitionDataCodec

/-!
# Production quotient-driver/codec bridge

Quotient declarations have the same one-root preseed shape as axioms, while
carrying a distinct payload discriminator and metadata constructor.  This
module verifies their actual singleton production path through serialization.
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

def compiledQuotientPayload (quotientVal : Ix.QuotVal)
    (typeExpr : Ixon.Expr) : Ixon.Quotient :=
  { kind := Ix.CompileM.convertQuotKind quotientVal.kind
    lvls := quotientVal.cnst.levelParams.size.toUInt64
    typ := typeExpr }

/-- The quotient metadata finalizer is total and preserves the primary
reference/universe tables. -/
theorem finishQuotientCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (quotientVal : Ix.QuotVal) (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishQuotientCompilation quotientVal
            typeExpr typeRoot) =
        .ok ((compiledQuotientPayload quotientVal typeExpr,
          constMeta, typeExpr), state') ∧
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
  let afterName := afterCache.compileName quotientVal.cnst.name
  let state' := afterName.compileNames quotientVal.cnst.levelParams
  let constMeta := { Ixon.ConstantMeta.new
      (.quot quotientVal.cnst.name.getHash
        (quotientVal.cnst.levelParams.map (·.getHash)) state.arena
        typeRoot) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  refine ⟨constMeta, state', ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterName :=
        BlockState.compileNames_exprTableView
          afterName quotientVal.cnst.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache quotientVal.cnst.name).tables
      _ = exprTableView state := rfl

def quotientCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (quotientVal : Ix.QuotVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := quotientVal.cnst.name
    univCtx := quotientVal.cnst.levelParams.toList }

theorem compileQuotient_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (quotientVal : Ix.QuotVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileQuotient quotientVal) =
      Ix.CompileM.CompileM.run compileEnv
        (quotientCompileBlockEnv blockEnv quotientVal)
        (axiomCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr quotientVal.cnst.type
          Ix.CompileM.finishQuotientCompilation quotientVal
            typeExpr typeRoot) := by
  rfl

theorem compileQuotient_run_of_compileExpr
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (quotientVal : Ix.QuotVal) (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (exprState : Ix.CompileM.BlockState)
    (hcompile : Ix.CompileM.CompileM.run compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal)
      (axiomCompileStartState state)
      (Ix.CompileM.compileExpr quotientVal.cnst.type) =
        .ok ((typeExpr, typeRoot), exprState)) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileQuotient quotientVal) =
        .ok ((compiledQuotientPayload quotientVal typeExpr,
          constMeta, typeExpr), state') ∧
      exprTableView state' = exprTableView exprState := by
  obtain ⟨constMeta, state', hfinish, htables⟩ :=
    finishQuotientCompilation_run compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal) exprState
      quotientVal typeExpr typeRoot
  refine ⟨constMeta, state', ?_, htables⟩
  rw [compileQuotient_run_eq, run_bind, hcompile]
  exact hfinish

/-- Ordinary quotient type compilation returns the exact reference-compiled
payload and preserves wire-safe primary tables. -/
theorem compileQuotient_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (quotientVal : Ix.QuotVal)
    {state : Ix.CompileM.BlockState} {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport quotientVal.cnst.type)
    (hbound : ExprWireBound quotientVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal) levelSupport snapshot
      (axiomCompileStartState state))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (quotientCompileBlockEnv blockEnv quotientVal) snapshot)
      quotientVal.cnst.type = some target) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileQuotient quotientVal) =
        .ok ((compiledQuotientPayload quotientVal target,
          constMeta, target), state') ∧
      BlockWireTablesWF state' ∧
      (compiledQuotientPayload quotientVal target).wireWF := by
  obtain ⟨typeRoot, exprState, hcompile, hexprState, htarget⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsource hbound hstate href
  obtain ⟨constMeta, state', hrun, htablesFrame⟩ :=
    compileQuotient_run_of_compileExpr compileEnv blockEnv state quotientVal
      target typeRoot exprState hcompile
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq (htablesFrame.trans hexprState.tables)
  exact ⟨constMeta, state', hrun, htables', htarget⟩

theorem compileQuotientBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (quotientVal : Ix.QuotVal)
    {state : Ix.CompileM.BlockState} {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport quotientVal.cnst.type)
    (hbound : ExprWireBound quotientVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal) levelSupport snapshot
      (axiomCompileStartState state))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (quotientCompileBlockEnv blockEnv quotientVal) snapshot)
      quotientVal.cnst.type = some target) :
    ∃ constMeta state',
      let info : Ixon.ConstantInfo :=
        .quot (compiledQuotientPayload quotientVal target)
      let result := Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state'.refs state'.univs)
        constMeta
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileQuotientBlock quotientVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hquotient, htables', hinfo⟩ :=
    compileQuotient_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables quotientVal hsource
      hbound hstate href
  have hfinish := finishConstantInfoWithSharing_run_codecWF
    compileEnv blockEnv state'
    (.quot (compiledQuotientPayload quotientVal target))
    constMeta hinfo htables'
  refine ⟨constMeta, state', ?_⟩
  dsimp only
  dsimp only at hfinish
  unfold Ix.CompileM.compileQuotientBlock
  rw [run_bind, hquotient]
  exact hfinish

theorem compileQuotientInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (quotientVal : Ix.QuotVal)
    (state preseedState : Ix.CompileM.BlockState) {target : Ixon.Expr}
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        #[(quotientVal.cnst.type,
            quotientVal.cnst.levelParams.toList)]) =
        .ok ((), preseedState))
    (hsource : SupportedOrdinaryExpr levelSupport quotientVal.cnst.type)
    (hbound : ExprWireBound quotientVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (quotientCompileBlockEnv blockEnv quotientVal) levelSupport snapshot
      (axiomCompileStartState preseedState))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (quotientCompileBlockEnv blockEnv quotientVal) snapshot)
      quotientVal.cnst.type = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileQuotientInfo quotientVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hrun, hcodec⟩ :=
    compileQuotientBlock_run_ordinary_codecWF compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables quotientVal hsource
      hbound hstate href
  let info : Ixon.ConstantInfo :=
    .quot (compiledQuotientPayload quotientVal target)
  let result := Ix.CompileM.BlockResult.mk'
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state'.refs state'.univs)
    constMeta
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileQuotientInfo
  rw [run_bind, hpreseed]
  exact hrun

def singletonQuotientBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (quotientVal : Ix.QuotVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert quotientVal.cnst.name 0 }

theorem auditConstantInfoPlanHeads_quotient_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (quotientVal : Ix.QuotVal) (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.quotInfo quotientVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities quotientVal.cnst.name
      quotientVal.cnst.type
    pure ()) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree _ _ _ _ _ hfree]
  exact run_pure compileEnv blockEnv state ()

theorem compileConstantInfo_quotient_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (quotientVal : Ix.QuotVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.quotInfo quotientVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonQuotientBlockEnv blockEnv quotientVal) state
        (Ix.CompileM.compileQuotientInfo quotientVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.quotInfo quotientVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert quotientVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileQuotientInfo quotientVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_quotient_run_surgeryFree
      compileEnv blockEnv state quotientVal hfree]
  simpa only [singletonQuotientBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      ((Std.TreeMap.empty : Ix.MutCtx).insert quotientVal.cnst.name 0)
      (Ix.CompileM.compileQuotientInfo quotientVal)

/-- Source readiness constructs the quotient's one-root preseed, frozen
reference target, production payload, and final codec-safe singleton block. -/
theorem compileConstantInfo_quotient_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (quotientVal : Ix.QuotVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hready : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonQuotientBlockEnv blockEnv quotientVal)
        quotientVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state)
      quotientVal.cnst.type)
    (htableBound : SingletonPreseedSourceBound
      (singletonQuotientBlockEnv blockEnv quotientVal) state
      quotientVal.cnst.type)
    (hbound : ExprWireBound quotientVal.cnst.type) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.quotInfo quotientVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonQuotientBlockEnv blockEnv quotientVal
  obtain ⟨preseedState, target, hpreseed, htables, href,
      hpreseedExpr, hpreseedCanon, hpreseedArena, hpreseedFinal⟩ :=
    preseedExprTables_singleton_run_ready_frozenRef compileEnv singletonEnv
      state quotientVal.cnst.levelParams.toList hclosed hlevelFaithful
      hexprFaithful hready hcanonCache hrefTable hunivTable htableBound
  have hexprPreseed : preseedState.exprCache = {} :=
    hpreseedExpr.trans hexprCache
  have hstate : FrozenExprStateWF compileEnv
      (quotientCompileBlockEnv singletonEnv quotientVal) levelSupport
      preseedState (axiomCompileStartState preseedState) :=
    axiomCompileStartState_frozen compileEnv
      (quotientCompileBlockEnv singletonEnv quotientVal) levelSupport
      preseedState hexprPreseed hpreseedCanon
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileQuotientInfo_run_ordinary_codecWF compileEnv singletonEnv
      preseedState hfree hclosed hlevelFaithful hexprFaithful htables
      quotientVal state preseedState hpreseed hready.supported hbound hstate
      href
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_quotient_run_surgeryFree_eq
    compileEnv blockEnv state quotientVal hfree]
  exact hrun

theorem compileConstantInfo_quotient_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (quotientVal : Ix.QuotVal)
    (hready : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonQuotientBlockEnv blockEnv quotientVal)
        quotientVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      quotientVal.cnst.type)
    (htableBound : SingletonPreseedSourceBound
      (singletonQuotientBlockEnv blockEnv quotientVal)
      (default : Ix.CompileM.BlockState) quotientVal.cnst.type)
    (hbound : ExprWireBound quotientVal.cnst.type) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.quotInfo quotientVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_quotient_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful quotientVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty hready htableBound
    hbound

end Ix.Compile.Verify
