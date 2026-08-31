import Ix.Compile.Verify.CompileRecursorCodec

/-!
# Production standalone-inductive/codec bridge

An inductive family compiles its type, drains that type's metadata, then
compiles every constructor under an independent arena while retaining one
frozen preseed table view.  The resulting inductive is wrapped in a one-member
mutual block with inductive and constructor projections.
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

private theorem run_getCompileEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getCompileEnv = .ok (compileEnv, state) := by
  rfl

def compiledConstructorPayload (constructorVal : Ix.ConstructorVal)
    (typeExpr : Ixon.Expr) : Ixon.Constructor :=
  { isUnsafe := constructorVal.isUnsafe
    lvls := constructorVal.cnst.levelParams.size.toUInt64
    cidx := constructorVal.cidx.toUInt64
    params := constructorVal.numParams.toUInt64
    fields := constructorVal.numFields.toUInt64
    typ := typeExpr }

theorem BlockState.compileNames_frozenFrame
    (state : Ix.CompileM.BlockState) (names : Array Ix.Name) :
    exprTableView (state.compileNames names) = exprTableView state ∧
      (state.compileNames names).exprCache = state.exprCache ∧
      (state.compileNames names).univCache = state.univCache ∧
      (state.compileNames names).canonUnivCache = state.canonUnivCache := by
  unfold Ix.CompileM.BlockState.compileNames
  apply Array.foldl_induction
    (motive := fun _ current =>
      exprTableView current = exprTableView state ∧
        current.exprCache = state.exprCache ∧
        current.univCache = state.univCache ∧
        current.canonUnivCache = state.canonUnivCache)
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i current hcurrent
    have hname := BlockState.compileName_frozenFrame current names[i]
    exact ⟨hname.1.trans hcurrent.1,
      hname.2.1.trans hcurrent.2.1,
      hname.2.2.1.trans hcurrent.2.2.1,
      hname.2.2.2.trans hcurrent.2.2.2⟩

theorem FrozenExprStateWF.withCurrent
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state) (current : Ix.Name) :
    FrozenExprStateWF compileEnv { blockEnv with current := current }
      levelSupport snapshot state := by
  refine {
    tables := hstate.tables
    exprCache := ?_
    univCache := ?_
    canonUnivCache := hstate.canonUnivCache }
  · simpa [frozenRefCompileCtx] using hstate.exprCache
  · simpa using hstate.univCache

/-- Constructor finalization is total, empties the context-sensitive
expression cache, and preserves the frozen tables and universe caches. -/
theorem finishConstructorCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (constructorVal : Ix.ConstructorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    ∃ ctorMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishConstructorCompilation constructorVal
            typeExpr typeRoot) =
        .ok ((compiledConstructorPayload constructorVal typeExpr,
          ctorMeta, typeExpr), state') ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = {} ∧
      state'.univCache = state.univCache ∧
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
  let afterName := afterCache.compileName constructorVal.cnst.name
  let state' := afterName.compileNames constructorVal.cnst.levelParams
  let ctorMeta := { Ixon.ConstantMeta.new
      (.ctor constructorVal.cnst.name.getHash
        (constructorVal.cnst.levelParams.map (·.getHash))
        constructorVal.induct.getHash state.arena typeRoot) with
      metaSharing := state.surgerySharing
      metaUnivs := state.metaUnivs
      univPatches := state.univPatches }
  refine ⟨ctorMeta, state', ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          constructorVal.cnst.levelParams
      _ = exprTableView afterCache :=
        (MetaStateFrame.compileName afterCache
          constructorVal.cnst.name).tables
      _ = exprTableView state := rfl
  ·
    have hlevels := BlockState.compileNames_frozenFrame afterName
      constructorVal.cnst.levelParams
    have hname := BlockState.compileName_frozenFrame afterCache
      constructorVal.cnst.name
    exact hlevels.2.1.trans (hname.2.1.trans rfl)
  ·
    have hlevels := BlockState.compileNames_frozenFrame afterName
      constructorVal.cnst.levelParams
    have hname := BlockState.compileName_frozenFrame afterCache
      constructorVal.cnst.name
    exact hlevels.2.2.1.trans (hname.2.2.1.trans rfl)
  ·
    have hlevels := BlockState.compileNames_frozenFrame afterName
      constructorVal.cnst.levelParams
    have hname := BlockState.compileName_frozenFrame afterCache
      constructorVal.cnst.name
    exact hlevels.2.2.2.trans (hname.2.2.2.trans rfl)

def constructorCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (constructorVal : Ix.ConstructorVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with current := constructorVal.cnst.name }

def constructorCompileStartState (state : Ix.CompileM.BlockState) :
    Ix.CompileM.BlockState :=
  { state with
    arena := {}
    metaUnivs := #[]
    metaUnivsIndex := {}
    univPatches := #[] }

theorem constructorCompileStartState_frozen
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (snapshot state : Ix.CompileM.BlockState)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (constructorCompileStartState state) := by
  exact hstate.of_frame rfl rfl rfl rfl

theorem compileConstructor_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (constructorVal : Ix.ConstructorVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstructor constructorVal) =
      Ix.CompileM.CompileM.run compileEnv
        (constructorCompileBlockEnv blockEnv constructorVal)
        (constructorCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr constructorVal.cnst.type
          Ix.CompileM.finishConstructorCompilation constructorVal
            typeExpr typeRoot) := by
  rfl

/-- One constructor compilation preserves a reusable frozen state for the
next constructor and returns a wire-safe payload. -/
theorem compileConstructor_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (constructorVal : Ix.ConstructorVal)
    {state : Ix.CompileM.BlockState} {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport constructorVal.cnst.type)
    (hbound : ExprWireBound constructorVal.cnst.type)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot)
      constructorVal.cnst.type = some target) :
    ∃ ctorMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstructor constructorVal) =
        .ok ((compiledConstructorPayload constructorVal target,
          ctorMeta, target), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (compiledConstructorPayload constructorVal target).wireWF ∧
      state'.exprCache = {} := by
  let ctorEnv := constructorCompileBlockEnv blockEnv constructorVal
  have hstateCtor : FrozenExprStateWF compileEnv ctorEnv levelSupport
      snapshot state := by
    exact hstate.withCurrent constructorVal.cnst.name
  have hstart : FrozenExprStateWF compileEnv ctorEnv levelSupport snapshot
      (constructorCompileStartState state) :=
    constructorCompileStartState_frozen compileEnv ctorEnv levelSupport
      snapshot state hstateCtor
  have hrefCtor : compileExprRef
      (frozenRefCompileCtx compileEnv ctorEnv snapshot)
      constructorVal.cnst.type = some target := by
    simpa [ctorEnv, constructorCompileBlockEnv, frozenRefCompileCtx] using
      href
  obtain ⟨typeRoot, exprState, hcompile, hexprState, htarget⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv ctorEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful hsource hbound hstart hrefCtor
  obtain ⟨ctorMeta, state', hfinish, htables, hexprCache,
      hunivCache, hcanonCache⟩ :=
    finishConstructorCompilation_run compileEnv ctorEnv exprState
      constructorVal target typeRoot
  have hfinalCtor : FrozenExprStateWF compileEnv ctorEnv levelSupport
      snapshot state' := by
    refine {
      tables := htables.trans hexprState.tables
      exprCache := ?_
      univCache := hexprState.univCache.of_cache_eq hunivCache
      canonUnivCache :=
        hexprState.canonUnivCache.of_cache_eq hcanonCache }
    apply OrdinaryExprCacheWF.of_cache_eq
      (OrdinaryExprCacheWF.empty
        (frozenRefCompileCtx compileEnv ctorEnv snapshot))
    exact hexprCache
  have hfinal : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state' := by
    simpa [ctorEnv, constructorCompileBlockEnv] using
      hfinalCtor.withCurrent blockEnv.current
  refine ⟨ctorMeta, state', ?_, hfinal, htarget, hexprCache⟩
  rw [compileConstructor_run_eq, run_bind, hcompile]
  exact hfinish

/-- The constructor list fold retains source order, frozen tables, payload
wire safety, root-array wire safety, and exact constructor count. -/
theorem compileInductiveConstructors_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (sourceCtors : List Ix.ConstructorVal)
    (acc : Ix.CompileM.InductiveConstructorCompileState)
    {state : Ix.CompileM.BlockState}
    (hsources : ∀ ctor ∈ sourceCtors,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type)
    (hbounds : ∀ ctor ∈ sourceCtors, ExprWireBound ctor.cnst.type)
    (hrefs : ∀ ctor ∈ sourceCtors, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv blockEnv snapshot) ctor.cnst.type =
          some target)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state)
    (hcache : state.exprCache = {})
    (haccCtors : ∀ ctor ∈ acc.ctors, ctor.wireWF)
    (haccExprs : ExprArrayWireWF acc.ctorExprs) :
    ∃ finalAcc state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveConstructors sourceCtors acc) =
        .ok (finalAcc, state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      finalAcc.ctors.size = acc.ctors.size + sourceCtors.length ∧
      (∀ ctor ∈ finalAcc.ctors, ctor.wireWF) ∧
      ExprArrayWireWF finalAcc.ctorExprs ∧
      state'.exprCache = {} := by
  induction sourceCtors generalizing acc state with
  | nil =>
      exact ⟨acc, state, run_pure compileEnv blockEnv state acc,
        hstate, by simp, haccCtors, haccExprs, hcache⟩
  | cons source rest ih =>
      have hsource : SupportedOrdinaryExpr levelSupport source.cnst.type :=
        hsources source (by simp)
      have hbound : ExprWireBound source.cnst.type :=
        hbounds source (by simp)
      obtain ⟨target, href⟩ := hrefs source (by simp)
      obtain ⟨ctorMeta, nextState, hctorRun, hnext, htarget, hnextCache⟩ :=
        compileConstructor_run_ordinary_wireWF compileEnv blockEnv snapshot
          hfree hclosed hlevelFaithful hexprFaithful source hsource hbound
          hstate href
      let compiledCtor := compiledConstructorPayload source target
      let nextAcc : Ix.CompileM.InductiveConstructorCompileState := {
        ctors := acc.ctors.push compiledCtor
        ctorMetaPairs := acc.ctorMetaPairs.push (source.cnst.name, ctorMeta)
        ctorNameAddrs := acc.ctorNameAddrs.push source.cnst.name.getHash
        ctorExprs := acc.ctorExprs.push target }
      have hnextCtors : ∀ ctor ∈ nextAcc.ctors, ctor.wireWF := by
        intro ctor hmem
        simp only [nextAcc, Array.mem_push] at hmem
        rcases hmem with hmem | rfl
        · exact haccCtors ctor hmem
        · exact htarget
      have hnextExprs : ExprArrayWireWF nextAcc.ctorExprs := by
        intro expr hmem
        simp only [nextAcc, Array.mem_push] at hmem
        rcases hmem with hmem | rfl
        · exact haccExprs expr hmem
        · exact htarget
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hsize,
          hfinalCtors, hfinalExprs, hfinalCache⟩ :=
        ih nextAcc (fun ctor hmem => hsources ctor (by simp [hmem]))
          (fun ctor hmem => hbounds ctor (by simp [hmem]))
          (fun ctor hmem => hrefs ctor (by simp [hmem])) hnext hnextCache
          hnextCtors hnextExprs
      refine ⟨finalAcc, finalState, ?_, hfinalState, ?_, hfinalCtors,
        hfinalExprs, hfinalCache⟩
      · unfold Ix.CompileM.compileInductiveConstructors
        rw [run_bind, hctorRun]
        exact hrestRun
      · dsimp only [nextAcc] at hsize
        simp only [Array.size_push] at hsize
        simp only [List.length_cons]
        omega

def capturedInductiveTypeMeta (state : Ix.CompileM.BlockState) :
    Ix.CompileM.InductiveTypeCompileMeta :=
  { arena := state.arena
    surgerySharing := state.surgerySharing
    metaUnivs := state.metaUnivs
    univPatches := state.univPatches }

def inductiveConstructorPhaseState (state : Ix.CompileM.BlockState) :
    Ix.CompileM.BlockState :=
  { state with
    arena := {}
    surgerySharing := #[]
    metaUnivs := #[]
    metaUnivsIndex := {}
    univPatches := #[]
    exprCache := {} }

theorem takeInductiveTypeCompileMeta_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.takeInductiveTypeCompileMeta =
      .ok (capturedInductiveTypeMeta state,
        inductiveConstructorPhaseState state) := by
  rfl

theorem inductiveConstructorPhaseState_frozen
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (snapshot state : Ix.CompileM.BlockState)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport
      snapshot state) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (inductiveConstructorPhaseState state) := by
  refine {
    tables := hstate.tables
    exprCache := ?_
    univCache := hstate.univCache.of_cache_eq rfl
    canonUnivCache := hstate.canonUnivCache.of_cache_eq rfl }
  apply OrdinaryExprCacheWF.of_cache_eq
    (OrdinaryExprCacheWF.empty
      (frozenRefCompileCtx compileEnv blockEnv snapshot))
  rfl

def compiledInductivePayload (inductiveVal : Ix.InductiveVal)
    (typeExpr : Ixon.Expr) (ctors : Array Ixon.Constructor) :
    Ixon.Inductive :=
  { isUnsafe := inductiveVal.isUnsafe
    lvls := inductiveVal.cnst.levelParams.size.toUInt64
    params := inductiveVal.numParams.toUInt64
    indices := inductiveVal.numIndices.toUInt64
    typ := typeExpr
    ctors }

private def inductiveMutNames (blockEnv : Ix.CompileM.BlockEnv) :
    Array Ix.Name :=
  blockEnv.mutCtx.toList.toArray.map (·.1)

private def inductiveMutCtxAddrs (blockEnv : Ix.CompileM.BlockEnv) :
    Array Address :=
  blockEnv.mutCtx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map
      (·.1.getHash)

/-- Inductive finalization assembles the captured type metadata and compiled
constructor arrays without changing primary expression tables. -/
theorem finishInductiveCompilation_run
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeMeta : Ix.CompileM.InductiveTypeCompileMeta)
    (compiledCtors : Ix.CompileM.InductiveConstructorCompileState) :
    ∃ indMeta state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishInductiveCompilation inductiveVal typeExpr
            typeRoot typeMeta compiledCtors) =
        .ok ((compiledInductivePayload inductiveVal typeExpr
            compiledCtors.ctors, indMeta, compiledCtors.ctorMetaPairs,
            compiledCtors.ctorExprs), state') ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.canonUnivCache = state.canonUnivCache := by
  let afterName := state.compileName inductiveVal.cnst.name
  let afterLevels := afterName.compileNames inductiveVal.cnst.levelParams
  let afterAll := afterLevels.compileNames inductiveVal.all
  let mutNames := inductiveMutNames blockEnv
  let state' := afterAll.compileNames mutNames
  let ctxAddrs := inductiveMutCtxAddrs blockEnv
  let indMeta := { Ixon.ConstantMeta.new
      (.indc inductiveVal.cnst.name.getHash
        (inductiveVal.cnst.levelParams.map (·.getHash))
        compiledCtors.ctorNameAddrs
        (inductiveVal.all.map (·.getHash)) ctxAddrs typeMeta.arena
        typeRoot) with
      metaSharing := typeMeta.surgerySharing
      metaUnivs := typeMeta.metaUnivs
      univPatches := typeMeta.univPatches }
  have hname := MetaStateFrame.compileName state inductiveVal.cnst.name
  have hlevels := MetaStateFrame.compileNames afterName
    inductiveVal.cnst.levelParams
  have hall := MetaStateFrame.compileNames afterLevels inductiveVal.all
  have hmut := MetaStateFrame.compileNames afterAll mutNames
  have hframe := hname.trans <| hlevels.trans <| hall.trans hmut
  refine ⟨indMeta, state', ?_, ?_, hframe.exprCache,
    hframe.canonUnivCache⟩
  · rfl
  · calc
      exprTableView state' = exprTableView afterAll :=
        BlockState.compileNames_exprTableView afterAll mutNames
      _ = exprTableView afterLevels :=
        BlockState.compileNames_exprTableView afterLevels inductiveVal.all
      _ = exprTableView afterName :=
        BlockState.compileNames_exprTableView afterName
          inductiveVal.cnst.levelParams
      _ = exprTableView state :=
        (MetaStateFrame.compileName state inductiveVal.cnst.name).tables

def inductiveCompileBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (inductiveVal : Ix.InductiveVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with
    current := inductiveVal.cnst.name
    univCtx := inductiveVal.cnst.levelParams.toList }

theorem compileInductive_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileInductive inductiveVal ctorVals) =
      Ix.CompileM.CompileM.run compileEnv
        (inductiveCompileBlockEnv blockEnv inductiveVal)
        (axiomCompileStartState state) (do
          let (typeExpr, typeRoot) ←
            Ix.CompileM.compileExpr inductiveVal.cnst.type
          let typeMeta ← Ix.CompileM.takeInductiveTypeCompileMeta
          let compiledCtors ← Ix.CompileM.compileInductiveConstructors
            ctorVals.toList { ctorExprs := #[typeExpr] }
          Ix.CompileM.finishInductiveCompilation inductiveVal typeExpr
            typeRoot typeMeta compiledCtors) := by
  rfl

/-- Sequential ordinary compilation of an inductive type and all constructor
types preserves the frozen preseed tables and produces a wire-safe inductive
plus a wire-safe sharing-root array. -/
theorem compileInductive_run_ordinary_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    {state : Ix.CompileM.BlockState}
    (htypeSource : SupportedOrdinaryExpr levelSupport inductiveVal.cnst.type)
    (hctorSources : ∀ ctor ∈ ctorVals.toList,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type)
    (htypeBound : ExprWireBound inductiveVal.cnst.type)
    (hctorBounds : ∀ ctor ∈ ctorVals.toList,
      ExprWireBound ctor.cnst.type)
    (hctorCount : ctorVals.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (inductiveCompileBlockEnv blockEnv inductiveVal) levelSupport snapshot
      (axiomCompileStartState state))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
      inductiveVal.cnst.type = some typeTarget)
    (hctorRefs : ∀ ctor ∈ ctorVals.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
        ctor.cnst.type = some target) :
    ∃ ind indMeta ctorMetaPairs ctorExprs state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductive inductiveVal ctorVals) =
        .ok ((ind, indMeta, ctorMetaPairs, ctorExprs), state') ∧
      BlockWireTablesWF state' ∧
      exprTableView state' = exprTableView snapshot ∧
      ind.wireWF ∧
      ExprArrayWireWF ctorExprs ∧
      state'.exprCache = {} ∧
      CanonUnivCacheWF state' := by
  let indEnv := inductiveCompileBlockEnv blockEnv inductiveVal
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
      snapshot hfree hclosed hlevelFaithful hexprFaithful ctorVals.toList
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
    finishInductiveCompilation_run compileEnv indEnv ctorState inductiveVal
      typeTarget typeRoot typeMeta compiledCtors
  let ind := compiledInductivePayload inductiveVal typeTarget
    compiledCtors.ctors
  have hcompiledSize : compiledCtors.ctors.size = ctorVals.size := by
    simpa using hctorSize
  have hindWire : ind.wireWF := by
    refine ⟨htypeWire, ?_, ?_⟩
    · simpa [ind, compiledInductivePayload, hcompiledSize] using hctorCount
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
  rw [compileInductive_run_eq, run_bind, htypeRun]
  simp only
  rw [run_bind, htake]
  simp only
  rw [run_bind, hctorsRun]
  exact hfinish

theorem finishInductiveFamilyBlock_run_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (ctorMetaPairs : Array (Ix.Name × Ixon.ConstantMeta))
    (ctorExprs : Array Ixon.Expr)
    (hind : ind.wireWF) (hroots : ExprArrayWireWF ctorExprs)
    (htables : BlockWireTablesWF state) :
    ∃ result,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.finishInductiveFamilyBlock inductiveVal ind indMeta
            ctorMetaPairs ctorExprs) =
        .ok (result, state) ∧
      BlockResultCodecWF result := by
  let info : Ixon.ConstantInfo := .muts #[.indc ind]
  have hinfo : info.wireWF := by
    refine ⟨?_, ?_⟩
    · change 1 < UInt64.size
      decide
    · intro member hmem
      have heq : member = .indc ind := by simpa [info] using hmem
      subst member
      exact hind
  let block := Ix.CompileM.buildConstantWithSharing
    info ctorExprs state.refs state.univs
  let blockAddr := Address.blake3 (Ixon.ser block)
  let projections := Ix.CompileM.buildInductiveProjections inductiveVal
    indMeta ctorMetaPairs blockAddr
  let result := Ix.CompileM.BlockResult.mk' block .empty projections
  have hblock : block.wireWF :=
    buildConstantWithSharing_wireWF info ctorExprs hinfo hroots htables
  refine ⟨result, ?_, BlockResult.mk'_codecWF block .empty projections hblock⟩
  rfl

theorem compileInductiveFamilyBlock_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    {state : Ix.CompileM.BlockState}
    (htypeSource : SupportedOrdinaryExpr levelSupport inductiveVal.cnst.type)
    (hctorSources : ∀ ctor ∈ ctorVals.toList,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type)
    (htypeBound : ExprWireBound inductiveVal.cnst.type)
    (hctorBounds : ∀ ctor ∈ ctorVals.toList,
      ExprWireBound ctor.cnst.type)
    (hctorCount : ctorVals.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (inductiveCompileBlockEnv blockEnv inductiveVal) levelSupport snapshot
      (axiomCompileStartState state))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
      inductiveVal.cnst.type = some typeTarget)
    (hctorRefs : ∀ ctor ∈ ctorVals.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
        ctor.cnst.type = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveFamilyBlock inductiveVal ctorVals) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨ind, indMeta, ctorMetaPairs, ctorExprs, state', hindRun,
      htables', _, hind, hroots, _, _⟩ :=
    compileInductive_run_ordinary_wireWF compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful htables inductiveVal ctorVals
      htypeSource hctorSources htypeBound hctorBounds hctorCount hstate
      htypeRef hctorRefs
  obtain ⟨result, hfinish, hcodec⟩ :=
    finishInductiveFamilyBlock_run_codecWF compileEnv blockEnv state'
      inductiveVal ind indMeta ctorMetaPairs ctorExprs hind hroots htables'
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileInductiveFamilyBlock
  rw [run_bind, hindRun]
  exact hfinish

theorem compileInductiveFamilyInfo_run_ordinary_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state preseedState : Ix.CompileM.BlockState)
    (hpreseed : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.inductivePreseedExprs inductiveVal ctorVals)) =
        .ok ((), preseedState))
    (htypeSource : SupportedOrdinaryExpr levelSupport inductiveVal.cnst.type)
    (hctorSources : ∀ ctor ∈ ctorVals.toList,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type)
    (htypeBound : ExprWireBound inductiveVal.cnst.type)
    (hctorBounds : ∀ ctor ∈ ctorVals.toList,
      ExprWireBound ctor.cnst.type)
    (hctorCount : ctorVals.size < UInt64.size)
    (hstate : FrozenExprStateWF compileEnv
      (inductiveCompileBlockEnv blockEnv inductiveVal) levelSupport snapshot
      (axiomCompileStartState preseedState))
    (htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
      inductiveVal.cnst.type = some typeTarget)
    (hctorRefs : ∀ ctor ∈ ctorVals.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (inductiveCompileBlockEnv blockEnv inductiveVal) snapshot)
        ctor.cnst.type = some target) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveFamilyInfo inductiveVal ctorVals) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileInductiveFamilyBlock_run_ordinary_codecWF compileEnv blockEnv
      snapshot hfree hclosed hlevelFaithful hexprFaithful htables
      inductiveVal ctorVals htypeSource hctorSources htypeBound hctorBounds
      hctorCount hstate htypeRef hctorRefs
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileInductiveFamilyInfo
  rw [run_bind, hpreseed]
  exact hrun

/-- Kernel inductive families use one universe-parameter ordering for the
inductive and all constructors. -/
def InductiveFamilyLevelParams (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal) : Prop :=
  ∀ ctor ∈ ctorVals,
    ctor.cnst.levelParams = inductiveVal.cnst.levelParams

theorem inductivePreseedExprs_eq_roots
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals) :
    Ix.CompileM.inductivePreseedExprs inductiveVal ctorVals =
      ((Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals).map
        (fun source =>
          (source, inductiveVal.cnst.levelParams.toList))).toArray := by
  have hmap :
      ctorVals.map (fun ctorVal =>
        (ctorVal.cnst.type, ctorVal.cnst.levelParams.toList)) =
      ctorVals.map (fun ctorVal =>
        (ctorVal.cnst.type, inductiveVal.cnst.levelParams.toList)) := by
    apply Array.ext
    · simp
    · intro idx hleft hright
      have hidx : idx < ctorVals.size := by simpa using hleft
      simp only [Array.getElem_map]
      rw [hparams ctorVals[idx] (Array.getElem_mem hidx)]
  unfold Ix.CompileM.inductivePreseedExprs
  rw [hmap]
  simp [Ix.CompileM.inductiveSourceExprs]

/-- A ready same-context inductive family constructs its complete production
preseed and compiles to a codec-safe one-member mutual block. -/
theorem compileInductiveFamilyInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state : Ix.CompileM.BlockState)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv
          inductiveVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound blockEnv state
      (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveFamilyInfo inductiveVal ctorVals) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let params := inductiveVal.cnst.levelParams.toList
  let rest := ctorVals.toList.map (·.cnst.type)
  have htypeMem : inductiveVal.cnst.type ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals := by
    simp [Ix.CompileM.inductiveSourceExprs]
  have hctorMem : ∀ ctor ∈ ctorVals.toList,
      ctor.cnst.type ∈
        Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals := by
    intro ctor hmem
    unfold Ix.CompileM.inductiveSourceExprs
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hmem, rfl⟩)
  have hrestReady : ∀ source ∈ rest,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) source := by
    intro source hmem
    apply hready source
    unfold Ix.CompileM.inductiveSourceExprs
    exact List.mem_cons_of_mem _ hmem
  obtain ⟨preseedState, hpreseed, htables, htargets, hexpr,
      hcanonState, harena, hfinal⟩ :=
    preseedExprTables_roots_run_ready_frozenRefs compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful inductiveVal.cnst.type
      rest (hready _ htypeMem) hrestReady hcanonCache hrefTable hunivTable
      htableBound
  have hpreseed' : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables
        (Ix.CompileM.inductivePreseedExprs inductiveVal ctorVals)) =
        .ok ((), preseedState) := by
    rw [inductivePreseedExprs_eq_roots inductiveVal ctorVals hparams]
    simpa [Ix.CompileM.inductiveSourceExprs, rest] using hpreseed
  have hexprPreseed : preseedState.exprCache = {} :=
    hexpr.trans hexprCache
  have hfrozen : FrozenExprStateWF compileEnv
      (inductiveCompileBlockEnv blockEnv inductiveVal) levelSupport
      preseedState (axiomCompileStartState preseedState) :=
    axiomCompileStartState_frozen compileEnv
      (inductiveCompileBlockEnv blockEnv inductiveVal) levelSupport
      preseedState hexprPreseed hcanonState
  have htypeRef : ∃ typeTarget, compileExprRef
      (frozenRefCompileCtx compileEnv
        (inductiveCompileBlockEnv blockEnv inductiveVal) preseedState)
      inductiveVal.cnst.type = some typeTarget := by
    obtain ⟨target, href⟩ := htargets inductiveVal.cnst.type
      List.mem_cons_self
    refine ⟨target, ?_⟩
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      inductiveCompileBlockEnv] using href
  have hctorRefs : ∀ ctor ∈ ctorVals.toList, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (inductiveCompileBlockEnv blockEnv inductiveVal) preseedState)
        ctor.cnst.type = some target := by
    intro ctor hmem
    have hctorRest : ctor.cnst.type ∈ rest :=
      List.mem_map.mpr ⟨ctor, hmem, rfl⟩
    obtain ⟨target, href⟩ := htargets ctor.cnst.type
      (List.mem_cons_of_mem _ hctorRest)
    refine ⟨target, ?_⟩
    simpa [params, frozenRefCompileCtx, preseedContextBlockEnv,
      inductiveCompileBlockEnv] using href
  have htypeSource :
      SupportedOrdinaryExpr levelSupport inductiveVal.cnst.type :=
    (hready _ htypeMem).supported
  have hctorSources : ∀ ctor ∈ ctorVals.toList,
      SupportedOrdinaryExpr levelSupport ctor.cnst.type := by
    intro ctor hmem
    exact (hready ctor.cnst.type (hctorMem ctor hmem)).supported
  have htypeBound : ExprWireBound inductiveVal.cnst.type :=
    hexprBounds _ htypeMem
  have hctorBounds : ∀ ctor ∈ ctorVals.toList,
      ExprWireBound ctor.cnst.type := by
    intro ctor hmem
    exact hexprBounds ctor.cnst.type (hctorMem ctor hmem)
  exact compileInductiveFamilyInfo_run_ordinary_codecWF compileEnv blockEnv
    preseedState hfree hclosed hlevelFaithful hexprFaithful htables
    inductiveVal ctorVals state preseedState hpreseed' htypeSource
    hctorSources htypeBound hctorBounds hctorCount hfrozen htypeRef
    hctorRefs

def InductiveConstructorLookup (compileEnv : Ix.CompileM.CompileEnv)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal) : Prop :=
  List.Forall₂ (fun name ctor =>
    compileEnv.env.get? name = some (.ctorInfo ctor))
    inductiveVal.ctors.toList ctorVals.toList

private theorem findConst_run_of_get
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) (constInfo : Ix.ConstantInfo)
    (hget : compileEnv.env.get? name = some constInfo) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.findConst name) = .ok (constInfo, state) := by
  unfold Ix.CompileM.findConst
  rw [run_bind, run_getCompileEnv]
  simp only
  rw [hget]
  rfl

theorem collectInductiveConstructors_run_of_lookup
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (names : List Ix.Name) (ctorVals : List Ix.ConstructorVal)
    (acc : Array Ix.ConstructorVal)
    (hlookup : List.Forall₂ (fun name ctor =>
      compileEnv.env.get? name = some (.ctorInfo ctor)) names ctorVals)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectInductiveConstructors names acc) =
      .ok (acc ++ ctorVals.toArray, state) := by
  induction hlookup generalizing acc with
  | nil =>
      simp [Ix.CompileM.collectInductiveConstructors, run_pure]
  | cons hget rest ih =>
      unfold Ix.CompileM.collectInductiveConstructors
      rw [run_bind,
        findConst_run_of_get compileEnv blockEnv state _ _ hget]
      simp only
      rw [run_bind,
        auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
          _ _ hfree]
      simp only
      rw [ih (acc := acc.push _)]
      congr 2
      rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem lookupInductiveConstructors_run_of_lookup
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.lookupInductiveConstructors inductiveVal) =
      .ok (ctorVals, state) := by
  unfold Ix.CompileM.lookupInductiveConstructors
  have hrun := collectInductiveConstructors_run_of_lookup compileEnv
    blockEnv state inductiveVal.ctors.toList ctorVals.toList #[] hlookup
    hfree
  simpa using hrun

def inductiveFamilyBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      Ix.CompileM.buildInductiveMutCtx inductiveVal ctorVals }

theorem compileInductiveInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state : Ix.CompileM.BlockState)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv blockEnv inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv blockEnv inductiveVal ctorVals) state
      (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileInductiveInfo inductiveVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  have hlookupRun := lookupInductiveConstructors_run_of_lookup compileEnv
    blockEnv state inductiveVal ctorVals hlookup hfree
  obtain ⟨result, state', hfamily, hcodec⟩ :=
    compileInductiveFamilyInfo_run_ready_codecWF compileEnv
      (inductiveFamilyBlockEnv blockEnv inductiveVal ctorVals) hfree hclosed
      hlevelFaithful hexprFaithful inductiveVal ctorVals state hexprCache
      hcanonCache hrefTable hunivTable hparams hready htableBound
      hexprBounds hctorCount
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileInductiveInfo
  rw [run_bind, hlookupRun]
  simpa only [inductiveFamilyBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      (Ix.CompileM.buildInductiveMutCtx inductiveVal ctorVals)
      (Ix.CompileM.compileInductiveFamilyInfo inductiveVal ctorVals) |>.trans
        hfamily

def singletonInductiveBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (inductiveVal : Ix.InductiveVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert inductiveVal.cnst.name 0 }

theorem auditConstantInfoPlanHeads_inductive_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.inductInfo inductiveVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities inductiveVal.cnst.name
      inductiveVal.cnst.type
    pure ()) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
      inductiveVal.cnst.name inductiveVal.cnst.type hfree]
  exact run_pure compileEnv blockEnv state ()

theorem compileConstantInfo_inductive_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (inductiveVal : Ix.InductiveVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.inductInfo inductiveVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonInductiveBlockEnv blockEnv inductiveVal) state
        (Ix.CompileM.compileInductiveInfo inductiveVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.inductInfo inductiveVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert inductiveVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileInductiveInfo inductiveVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_inductive_run_surgeryFree compileEnv blockEnv
      state inductiveVal hfree]
  simpa only [singletonInductiveBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      ((Std.TreeMap.empty : Ix.MutCtx).insert inductiveVal.cnst.name 0)
      (Ix.CompileM.compileInductiveInfo inductiveVal)

theorem compileConstantInfo_inductive_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state : Ix.CompileM.BlockState)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv
            (singletonInductiveBlockEnv blockEnv inductiveVal)
            inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv
        (singletonInductiveBlockEnv blockEnv inductiveVal)
        inductiveVal ctorVals)
      state (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.inductInfo inductiveVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonInductiveBlockEnv blockEnv inductiveVal
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileInductiveInfo_run_ready_codecWF compileEnv singletonEnv hfree
      hclosed hlevelFaithful hexprFaithful inductiveVal ctorVals state
      hlookup hexprCache hcanonCache hrefTable hunivTable hparams hready
      htableBound hexprBounds hctorCount
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_inductive_run_surgeryFree_eq compileEnv blockEnv
    state inductiveVal hfree]
  exact hrun

theorem compileConstantInfo_inductive_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv
            (singletonInductiveBlockEnv blockEnv inductiveVal)
            inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport
        (preseedContextStartState (default : Ix.CompileM.BlockState))
        source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv
        (singletonInductiveBlockEnv blockEnv inductiveVal)
        inductiveVal ctorVals)
      (default : Ix.CompileM.BlockState)
      (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.inductInfo inductiveVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_inductive_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful inductiveVal ctorVals
    (default : Ix.CompileM.BlockState) hlookup rfl CanonUnivCacheWF.empty
    PreseedRefTableWF.empty PreseedUnivTableWF.empty hparams hready
    htableBound hexprBounds hctorCount

def ConstructorParentLookup (compileEnv : Ix.CompileM.CompileEnv)
    (constructorVal : Ix.ConstructorVal)
    (inductiveVal : Ix.InductiveVal) : Prop :=
  compileEnv.env.get? constructorVal.induct = some (.inductInfo inductiveVal)

theorem compileConstructorInfo_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (constructorVal : Ix.ConstructorVal)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state : Ix.CompileM.BlockState)
    (hparent : ConstructorParentLookup compileEnv constructorVal inductiveVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv blockEnv inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv blockEnv inductiveVal ctorVals) state
      (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstructorInfo constructorVal) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  have hparentRun := findConst_run_of_get compileEnv blockEnv state
    constructorVal.induct (.inductInfo inductiveVal) hparent
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileInductiveInfo_run_ready_codecWF compileEnv blockEnv hfree hclosed
      hlevelFaithful hexprFaithful inductiveVal ctorVals state hlookup
      hexprCache hcanonCache hrefTable hunivTable hparams hready htableBound
      hexprBounds hctorCount
  refine ⟨result, state', ?_, hcodec⟩
  unfold Ix.CompileM.compileConstructorInfo
  rw [run_bind, hparentRun]
  exact hrun

def singletonConstructorBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (constructorVal : Ix.ConstructorVal) : Ix.CompileM.BlockEnv :=
  { blockEnv with mutCtx :=
      (Std.TreeMap.empty : Ix.MutCtx).insert constructorVal.cnst.name 0 }

theorem auditConstantInfoPlanHeads_constructor_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (constructorVal : Ix.ConstructorVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.auditConstantInfoPlanHeads (.ctorInfo constructorVal)) =
      .ok ((), state) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditPlanHeadArities constructorVal.cnst.name
      constructorVal.cnst.type
    pure ()) = .ok ((), state)
  rw [run_bind,
    auditPlanHeadArities_run_surgeryFree compileEnv blockEnv state
      constructorVal.cnst.name constructorVal.cnst.type hfree]
  exact run_pure compileEnv blockEnv state ()

theorem compileConstantInfo_constructor_run_surgeryFree_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (constructorVal : Ix.ConstructorVal)
    (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileConstantInfo (.ctorInfo constructorVal)) =
      Ix.CompileM.CompileM.run compileEnv
        (singletonConstructorBlockEnv blockEnv constructorVal) state
        (Ix.CompileM.compileConstructorInfo constructorVal) := by
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    Ix.CompileM.auditConstantInfoPlanHeads (.ctorInfo constructorVal)
    let mutCtx : Ix.MutCtx :=
      Std.TreeMap.empty.insert constructorVal.cnst.name 0
    Ix.CompileM.withMutCtx mutCtx
      (Ix.CompileM.compileConstructorInfo constructorVal)) = _
  rw [run_bind,
    auditConstantInfoPlanHeads_constructor_run_surgeryFree compileEnv
      blockEnv state constructorVal hfree]
  simpa only [singletonConstructorBlockEnv] using
    run_withMutCtx compileEnv blockEnv state
      ((Std.TreeMap.empty : Ix.MutCtx).insert constructorVal.cnst.name 0)
      (Ix.CompileM.compileConstructorInfo constructorVal)

theorem compileConstantInfo_constructor_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (constructorVal : Ix.ConstructorVal)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (state : Ix.CompileM.BlockState)
    (hparent : ConstructorParentLookup compileEnv constructorVal inductiveVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hexprCache : state.exprCache = {})
    (hcanonCache : CanonUnivCacheWF state)
    (hrefTable : PreseedRefTableWF state)
    (hunivTable : PreseedUnivTableWF state)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv
            (singletonConstructorBlockEnv blockEnv constructorVal)
            inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport (preseedContextStartState state) source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv
        (singletonConstructorBlockEnv blockEnv constructorVal)
        inductiveVal ctorVals)
      state (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileConstantInfo (.ctorInfo constructorVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  let singletonEnv := singletonConstructorBlockEnv blockEnv constructorVal
  obtain ⟨result, state', hrun, hcodec⟩ :=
    compileConstructorInfo_run_ready_codecWF compileEnv singletonEnv hfree
      hclosed hlevelFaithful hexprFaithful constructorVal inductiveVal
      ctorVals state hparent hlookup hexprCache hcanonCache hrefTable
      hunivTable hparams hready htableBound hexprBounds hctorCount
  refine ⟨result, state', ?_, hcodec⟩
  rw [compileConstantInfo_constructor_run_surgeryFree_eq compileEnv blockEnv
    state constructorVal hfree]
  exact hrun

theorem compileConstantInfo_constructor_default_run_ready_codecWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (constructorVal : Ix.ConstructorVal)
    (inductiveVal : Ix.InductiveVal)
    (ctorVals : Array Ix.ConstructorVal)
    (hparent : ConstructorParentLookup compileEnv constructorVal inductiveVal)
    (hlookup : InductiveConstructorLookup compileEnv inductiveVal ctorVals)
    (hparams : InductiveFamilyLevelParams inductiveVal ctorVals)
    (hready : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      PreseedReady compileEnv
        (preseedContextBlockEnv
          (inductiveFamilyBlockEnv
            (singletonConstructorBlockEnv blockEnv constructorVal)
            inductiveVal ctorVals)
          inductiveVal.cnst.levelParams.toList)
        levelSupport
        (preseedContextStartState (default : Ix.CompileM.BlockState))
        source)
    (htableBound : RootPreseedSourceBound
      (inductiveFamilyBlockEnv
        (singletonConstructorBlockEnv blockEnv constructorVal)
        inductiveVal ctorVals)
      (default : Ix.CompileM.BlockState)
      (Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals))
    (hexprBounds : ∀ source ∈
      Ix.CompileM.inductiveSourceExprs inductiveVal ctorVals,
      ExprWireBound source)
    (hctorCount : ctorVals.size < UInt64.size) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv
          (default : Ix.CompileM.BlockState)
          (Ix.CompileM.compileConstantInfo (.ctorInfo constructorVal)) =
        .ok (result, state') ∧
      BlockResultCodecWF result := by
  apply compileConstantInfo_constructor_run_ready_codecWF compileEnv blockEnv
    hfree hclosed hlevelFaithful hexprFaithful constructorVal inductiveVal
    ctorVals (default : Ix.CompileM.BlockState) hparent hlookup rfl
    CanonUnivCacheWF.empty PreseedRefTableWF.empty PreseedUnivTableWF.empty
    hparams hready htableBound hexprBounds hctorCount

end Ix.Compile.Verify
