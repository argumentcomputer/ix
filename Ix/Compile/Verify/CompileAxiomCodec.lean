import Ix.Compile.Verify.CompileSharingCodec
import Ix.Compile.Verify.CompilePreseed

/-!
# Production axiom-driver/codec bridge

This layer verifies the production `compileAxiom` wrapper around ordinary
expression compilation.  It isolates the metadata/name finalizer, proves that
the finalizer preserves the primary expression tables, and composes the
resulting wire-safe axiom with the canonical sharing/`BlockResult` tail.
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

private theorem run_getCompileEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getCompileEnv = .ok (compileEnv, state) := by
  rfl

theorem BlockState.compileNames_exprTableView
    (state : Ix.CompileM.BlockState) (names : Array Ix.Name) :
    exprTableView (state.compileNames names) = exprTableView state := by
  unfold Ix.CompileM.BlockState.compileNames
  apply Array.foldl_induction
    (motive := fun _ current =>
      exprTableView current = exprTableView state)
  · rfl
  · intro i current hcurrent
    exact (MetaStateFrame.compileName current names[i]).tables.trans hcurrent

theorem compileNames_run (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (names : Array Ix.Name) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileNames names) =
      .ok ((), state.compileNames names) := by
  rfl

def compiledAxiomPayload (axiomVal : Ix.AxiomVal)
    (typeExpr : Ixon.Expr) : Ixon.Axiom :=
  { isUnsafe := axiomVal.isUnsafe
    lvls := axiomVal.cnst.levelParams.size.toUInt64
    typ := typeExpr }

/-- The axiom metadata finalizer cannot fail, returns the already compiled
type in both payload positions, and changes no primary expression table. -/
theorem finishAxiomCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (axiomVal : Ix.AxiomVal) (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishAxiomCompilation axiomVal typeExpr typeRoot) =
        .ok ((compiledAxiomPayload axiomVal typeExpr,
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
  let afterName := afterCache.compileName axiomVal.cnst.name
  let state' := afterName.compileNames axiomVal.cnst.levelParams
  let constMeta := { Ixon.ConstantMeta.new
      (.axio axiomVal.cnst.name.getHash
        (axiomVal.cnst.levelParams.map (·.getHash)) state.arena typeRoot) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  refine ⟨constMeta, state', ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterName :=
        BlockState.compileNames_exprTableView
          afterName axiomVal.cnst.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache axiomVal.cnst.name).tables
      _ = exprTableView state := rfl

/-- Reader context in which production compiles an axiom type. -/
def axiomCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (axiomVal : Ix.AxiomVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := axiomVal.cnst.name
    univCtx := axiomVal.cnst.levelParams.toList }

/-- State after the cache/context reset performed immediately before
`compileAxiom` invokes `compileExpr`. -/
def axiomCompileStartState (state : Ix.CompileM.BlockState) :
    Ix.CompileM.BlockState :=
  { state with
    univCache := {}
    arena := {}
    metaUnivs := #[]
    metaUnivsIndex := {}
    univPatches := #[] }

@[simp] theorem axiomCompileStartState_exprTableView
    (state : Ix.CompileM.BlockState) :
    exprTableView (axiomCompileStartState state) = exprTableView state := by
  rfl

/-- A completed preseed state with an empty expression cache and sound
canonical-universe memo supplies the complete frozen state required by the
axiom expression phase. The axiom reset itself empties the context-sensitive
universe cache while retaining the finished primary tables. -/
theorem axiomCompileStartState_frozen
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (state : Ix.CompileM.BlockState)
    (hexpr : state.exprCache = {})
    (hcanon : CanonUnivCacheWF state) :
    FrozenExprStateWF compileEnv blockEnv levelSupport state
      (axiomCompileStartState state) := by
  refine
    { tables := axiomCompileStartState_exprTableView state
      exprCache := ?_
      univCache := ?_
      canonUnivCache := ?_ }
  · apply OrdinaryExprCacheWF.of_cache_eq
      (OrdinaryExprCacheWF.empty
        (frozenRefCompileCtx compileEnv blockEnv state))
    change state.exprCache =
      ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64))
    exact hexpr
  · apply UnivCacheWF.of_cache_eq
      (UnivCacheWF.empty (univParamIndex blockEnv.univCtx) levelSupport)
    rfl
  · exact hcanon.of_cache_eq rfl

/-- Definitional decomposition of the production axiom compiler into its
state/context reset, one expression compilation, and the named finalizer. -/
theorem compileAxiom_run_eq (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (axiomVal : Ix.AxiomVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileAxiom axiomVal) =
      Ix.CompileM.CompileM.run compileEnv
        (axiomCompileBlockEnv blockEnv axiomVal)
        (axiomCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr axiomVal.cnst.type
          Ix.CompileM.finishAxiomCompilation axiomVal typeExpr typeRoot) := by
  rfl

/-- Any successful production type-expression phase determines the complete
`compileAxiom` result: the payload contains that exact expression and the
metadata finalizer preserves its final primary tables. -/
theorem compileAxiom_run_of_compileExpr
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (axiomVal : Ix.AxiomVal) (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (exprState : Ix.CompileM.BlockState)
    (hcompile : Ix.CompileM.CompileM.run compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal)
      (axiomCompileStartState state)
      (Ix.CompileM.compileExpr axiomVal.cnst.type) =
        .ok ((typeExpr, typeRoot), exprState)) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAxiom axiomVal) =
        .ok ((compiledAxiomPayload axiomVal typeExpr,
          constMeta, typeExpr), state') ∧
      exprTableView state' = exprTableView exprState := by
  obtain ⟨constMeta, state', hfinish, htables⟩ :=
    finishAxiomCompilation_run compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal) exprState
      axiomVal typeExpr typeRoot
  refine ⟨constMeta, state', ?_, htables⟩
  rw [compileAxiom_run_eq, run_bind, hcompile]
  exact hfinish

/-- On the verified ordinary-expression domain, production `compileAxiom`
returns the exact reference-compiled type, a wire-safe axiom payload, and a
final state whose primary reference/universe tables remain wire-safe. -/
theorem compileAxiom_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot) (axiomVal : Ix.AxiomVal)
    {state : Ix.CompileM.BlockState} {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal) levelSupport snapshot
      (axiomCompileStartState state))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (axiomCompileBlockEnv blockEnv axiomVal) snapshot)
      axiomVal.cnst.type = some target) :
    ∃ constMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAxiom axiomVal) =
        .ok ((compiledAxiomPayload axiomVal target,
          constMeta, target), state') ∧
      BlockWireTablesWF state' ∧
      (compiledAxiomPayload axiomVal target).wireWF := by
  obtain ⟨typeRoot, exprState, hcompile, hexprState, htarget⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsource hbound hstate href
  obtain ⟨constMeta, state', hrun, htablesFrame⟩ :=
    compileAxiom_run_of_compileExpr compileEnv blockEnv state axiomVal
      target typeRoot exprState hcompile
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq (htablesFrame.trans hexprState.tables)
  refine ⟨constMeta, state', hrun, htables', ?_⟩
  exact htarget

/-- The actual singleton-axiom branch body—payload compilation followed by
canonical sharing and `BlockResult` serialization—returns an exactly
decodable main block on the verified ordinary-expression domain. -/
theorem compileAxiomBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot) (axiomVal : Ix.AxiomVal)
    {state : Ix.CompileM.BlockState} {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal) levelSupport snapshot
      (axiomCompileStartState state))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (axiomCompileBlockEnv blockEnv axiomVal) snapshot)
      axiomVal.cnst.type = some target) :
    ∃ constMeta state',
      let info : Ixon.ConstantInfo :=
        .axio (compiledAxiomPayload axiomVal target)
      let result := Ix.CompileM.BlockResult.mk'
        (Ix.CompileM.buildConstantWithSharing info
          (Ix.CompileM.constantInfoRootExprs info)
          state'.refs state'.univs)
        constMeta
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAxiomBlock axiomVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', haxiom, htables', hinfo⟩ :=
    compileAxiom_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables axiomVal hsource hbound
      hstate href
  have hfinish := finishConstantInfoWithSharing_run_codecWF
    compileEnv blockEnv state'
    (.axio (compiledAxiomPayload axiomVal target)) constMeta hinfo htables'
  refine ⟨constMeta, state', ?_⟩
  dsimp only
  dsimp only at hfinish
  unfold Ix.CompileM.compileAxiomBlock
  rw [run_bind, haxiom]
  exact hfinish

/-- Block environment installed by the singleton declaration driver before
dispatching an axiom payload. -/
def singletonAxiomBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (axiomVal : Ix.AxiomVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert axiomVal.cnst.name 0 }

/-- With no surgery plans, the production head-arity audit takes its
read-only fast path for every expression. -/
theorem auditPlanHeadArities_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (owner : Ix.Name) (source : Ix.Expr)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditPlanHeadArities owner source) =
      .ok ((), state) := by
  simp only [Ix.CompileM.CompileEnv.surgeryFree,
    Bool.and_eq_true] at hfree
  rw [Ix.CompileM.auditPlanHeadArities, run_bind, run_getCompileEnv]
  simp only
  rw [hfree.1.1, hfree.2, hfree.1.2]
  rfl

theorem auditConstantInfoPlanHeads_axiom_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (axiomVal : Ix.AxiomVal) (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.axiomInfo axiomVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities axiomVal.cnst.name axiomVal.cnst.type
    pure ()) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree _ _ _ _ _ hfree]
  exact run_pure compileEnv blockEnv state ()

/-- The preseeded production axiom phase inherits the complete codec
postcondition of `compileAxiomBlock`.  The preseed transition remains an
explicit hypothesis until its table construction is verified. -/
theorem compileAxiomInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot) (axiomVal : Ix.AxiomVal)
    (state preseedState : Ix.CompileM.BlockState) {target : Ixon.Expr}
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        #[(axiomVal.cnst.type, axiomVal.cnst.levelParams.toList)]) =
        .ok ((), preseedState))
    (hsource : SupportedOrdinaryExpr levelSupport axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (axiomCompileBlockEnv blockEnv axiomVal) levelSupport snapshot
      (axiomCompileStartState preseedState))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (axiomCompileBlockEnv blockEnv axiomVal) snapshot)
      axiomVal.cnst.type = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAxiomInfo axiomVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨constMeta, state', hrun, hcodec⟩ :=
    compileAxiomBlock_run_ordinary_codecWF compileEnv blockEnv snapshot
      hfree hclosed hlevelFaithful hexprFaithful htables axiomVal hsource
      hbound hstate href
  let info : Ixon.ConstantInfo :=
    .axio (compiledAxiomPayload axiomVal target)
  let result := Ix.CompileM.BlockResult.mk'
    (Ix.CompileM.buildConstantWithSharing info
      (Ix.CompileM.constantInfoRootExprs info)
      state'.refs state'.univs)
    constMeta
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileAxiomInfo
  rw [run_bind, hpreseed]
  exact hrun

/-- Exact production decomposition of the axiom case of
`compileConstantInfo`: common audit, singleton mutual context, then the named
preseed/compile/finalize phase. -/
theorem compileConstantInfo_axiom_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (axiomVal : Ix.AxiomVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.axiomInfo axiomVal)) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.auditConstantInfoPlanHeads (.axiomInfo axiomVal)) with
      | .error err => .error err
      | .ok (_, state') =>
        Ix.CompileM.CompileM.run compileEnv
          (singletonAxiomBlockEnv blockEnv axiomVal) state'
          (Ix.CompileM.compileAxiomInfo axiomVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state
    (Ix.CompileM.compileConstantInfoCore (.axiomInfo axiomVal)) = _
  rw [Ix.CompileM.compileConstantInfoCore, run_bind]
  generalize Ix.CompileM.CompileM.run compileEnv blockEnv state
    (Ix.CompileM.auditConstantInfoPlanHeads (.axiomInfo axiomVal)) = result
  cases result with
  | error err => rfl
  | ok result =>
    rcases result with ⟨value, state'⟩
    rfl

/-- Conditional end-to-end theorem for the actual singleton axiom dispatch.
The surgery-free audit, compilation, sharing, and codec obligations are
discharged; the remaining transition hypothesis exposes precisely the
table-preseed frontier. -/
theorem compileConstantInfo_axiom_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot) (axiomVal : Ix.AxiomVal)
    (state preseedState : Ix.CompileM.BlockState) {target : Ixon.Expr}
    (hpreseed : Ix.CompileM.CompileM.run compileEnv
      (singletonAxiomBlockEnv blockEnv axiomVal) state
      (Ix.CompileM.preseedExprTables
        #[(axiomVal.cnst.type, axiomVal.cnst.levelParams.toList)]) =
        .ok ((), preseedState))
    (hsource : SupportedOrdinaryExpr levelSupport axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv
      (axiomCompileBlockEnv
        (singletonAxiomBlockEnv blockEnv axiomVal) axiomVal)
      levelSupport snapshot (axiomCompileStartState preseedState))
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv
        (axiomCompileBlockEnv
          (singletonAxiomBlockEnv blockEnv axiomVal) axiomVal)
        snapshot)
      axiomVal.cnst.type = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.axiomInfo axiomVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileAxiomInfo_run_ordinary_codecWF compileEnv
      (singletonAxiomBlockEnv blockEnv axiomVal) snapshot hfree hclosed
      hlevelFaithful hexprFaithful htables axiomVal state preseedState
      hpreseed hsource hbound hstate href
  refine ⟨result, state', ?_, hcodec⟩
  have haudit := auditConstantInfoPlanHeads_axiom_run_surgeryFree
    compileEnv blockEnv state axiomVal hfree
  rw [compileConstantInfo_axiom_run_eq, haudit]
  exact hrun

/-- The remaining semantic postcondition on the committed singleton tables:
the frozen reference compiler can find every leaf of the axiom type. -/
def AxiomPreseedReferencePost
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (axiomVal : Ix.AxiomVal)
    (preseedState : Ix.CompileM.BlockState) : Prop :=
  ∃ target, compileExprRef
      (frozenRefCompileCtx compileEnv
        (axiomCompileBlockEnv
          (singletonAxiomBlockEnv blockEnv axiomVal) axiomVal)
        preseedState)
      axiomVal.cnst.type = some target

/-- Aggregate retained for clients that need both the constructed wire-table
invariant and semantic reference coverage. -/
def AxiomPreseedCodecPost
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (axiomVal : Ix.AxiomVal)
    (preseedState : Ix.CompileM.BlockState) : Prop :=
  BlockWireTablesWF preseedState ∧
    AxiomPreseedReferencePost compileEnv blockEnv axiomVal preseedState

/-- Actual singleton axiom dispatch with the raw preseed execution and manual
`FrozenExprStateWF` hypotheses discharged. A wire-ready source and explicit
source cardinality bound construct the entire preseed run, its primary wire
  tables, committed indexes, cache invariants, and raw-array source coverage. -/
theorem compileConstantInfo_axiom_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (axiomVal : Ix.AxiomVal) (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hready : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonAxiomBlockEnv blockEnv axiomVal)
        axiomVal.cnst.levelParams.toList)
      levelSupport (preseedContextStartState state) axiomVal.cnst.type)
    (htableBound : SingletonPreseedSourceBound
      (singletonAxiomBlockEnv blockEnv axiomVal) state axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.axiomInfo axiomVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonAxiomBlockEnv blockEnv axiomVal
  obtain ⟨preseedState, target, hpreseed, htables, href,
      hpreseedExpr, hpreseedCanon, hpreseedArena, hpreseedFinal⟩ :=
    preseedExprTables_singleton_run_ready_frozenRef compileEnv singletonEnv
      state axiomVal.cnst.levelParams.toList hclosed hlevelFaithful
      hexprFaithful hready hcanonCache hrefTable hunivTable htableBound
  have hexprPreseed : preseedState.exprCache = {} :=
    hpreseedExpr.trans hexprCache
  have hstate : FrozenExprStateWF compileEnv
      (axiomCompileBlockEnv singletonEnv axiomVal) levelSupport preseedState
      (axiomCompileStartState preseedState) :=
    axiomCompileStartState_frozen compileEnv
      (axiomCompileBlockEnv singletonEnv axiomVal) levelSupport preseedState
      hexprPreseed hpreseedCanon
  exact compileConstantInfo_axiom_run_ordinary_codecWF compileEnv blockEnv
    preseedState hfree hclosed hlevelFaithful hexprFaithful htables axiomVal
    state preseedState hpreseed hready.supported hbound hstate href

/-- Driver-shaped specialization: production begins every SCC block from the
default block state, whose expression/canonical caches are empty and sound. -/
theorem compileConstantInfo_axiom_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (axiomVal : Ix.AxiomVal)
    (hready : PreseedReady compileEnv
      (preseedContextBlockEnv
        (singletonAxiomBlockEnv blockEnv axiomVal)
        axiomVal.cnst.levelParams.toList)
      levelSupport
      (preseedContextStartState (default : Ix.CompileM.BlockState))
      axiomVal.cnst.type)
    (htableBound : SingletonPreseedSourceBound
      (singletonAxiomBlockEnv blockEnv axiomVal)
      (default : Ix.CompileM.BlockState) axiomVal.cnst.type)
    (hbound : ExprWireBound axiomVal.cnst.type) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.axiomInfo axiomVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_axiom_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful axiomVal
    (default : Ix.CompileM.BlockState) rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty hready htableBound
    hbound

end Ix.Compile.Verify
