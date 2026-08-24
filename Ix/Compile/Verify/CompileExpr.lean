import Ix.Compile.Verify.CompileUniv
import Ix.Compile.Verify.SourceValue
import Std.Data.HashMap.Lemmas

/-!
# Production ordinary-expression refinement

The full production expression compiler retains an opaque call-site-surgery
state machine.  When the compile environment has no surgery plans, its public
entry point now selects a fuel-total implementation with the same flattened
App, expression-cache, and arena allocation order.  This module starts the
refinement proof at that kernel-visible boundary.

The first closed fragment below covers the recursive structural core:
variables, applications, lambdas, foralls, lets, and erased empty metadata.
It proves cache hits and misses against `compileExprRef`, including flattened
application spines, under an explicit finite-support digest-faithfulness
premise.  Table-backed leaves are layered on this state-machine theorem next.
-/

namespace Ix.Compile.Verify

local instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

local instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

/-- Digest equality on expressions is an equivalence even though it need not
imply structural equality. -/
local instance : EquivBEq Ix.Expr where
  rfl {expr} := by
    change expr.getHash == expr.getHash
    exact BEq.rfl
  symm {left right} h := by
    change left.getHash == right.getHash at h
    change right.getHash == left.getHash
    exact beq_of_eq (eq_of_beq h).symm
  trans {left middle right} hleft hright := by
    change left.getHash == middle.getHash at hleft
    change middle.getHash == right.getHash at hright
    change left.getHash == right.getHash
    exact beq_of_eq ((eq_of_beq hleft).trans (eq_of_beq hright))

local instance : LawfulHashable Ix.Expr where
  hash_eq left right h := by
    change hash left.getHash = hash right.getHash
    exact LawfulHashable.hash_eq left.getHash right.getHash h

/-- No supported cached expression shares its digest with a structurally
different query.  This is the exact finite-run premise needed to reason about
the production expression hash map. -/
def ExprKeyFaithfulOn (support : Ix.Expr → Prop) : Prop :=
  ∀ {stored queried}, support stored → (stored == queried) = true →
    stored = queried

/-- The first production fragment: recursive expression structure without
table-backed leaves. Empty metadata is included because it exercises metadata
erasure and arena wrapping without introducing KV-map serialization effects. -/
inductive StructuralExpr : Ix.Expr → Prop where
  | bvar {idx hash} : StructuralExpr (.bvar idx hash)
  | app {fn arg hash} : StructuralExpr fn → StructuralExpr arg →
      StructuralExpr (.app fn arg hash)
  | lam {name ty body bi hash} : StructuralExpr ty → StructuralExpr body →
      StructuralExpr (.lam name ty body bi hash)
  | all {name ty body bi hash} : StructuralExpr ty → StructuralExpr body →
      StructuralExpr (.forallE name ty body bi hash)
  | letE {name ty val body nonDep hash} :
      StructuralExpr ty → StructuralExpr val → StructuralExpr body →
      StructuralExpr (.letE name ty val body nonDep hash)
  | mdata {inner hash} : StructuralExpr inner →
      StructuralExpr (.mdata #[] inner hash)

/-- Every production expression-cache entry in this slice came from the same
reference compiler and belongs to the supported structural fragment. -/
structure StructuralExprCacheWF (ctx : RefCompileCtx)
    (state : Ix.CompileM.BlockState) : Prop where
  supported : ∀ {source target root},
    state.exprCache.get? source = some (target, root) → StructuralExpr source
  sound : ∀ {source target root},
    state.exprCache.get? source = some (target, root) →
      compileExprRef ctx source = some target

theorem StructuralExprCacheWF.empty (ctx : RefCompileCtx) :
    StructuralExprCacheWF ctx (default : Ix.CompileM.BlockState) := by
  constructor <;> intro source target root h
  · change ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64)).get? source =
      some (target, root) at h
    simp at h
  · change ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64)).get? source =
      some (target, root) at h
    simp at h

/-- Updating fields other than the expression cache preserves cache
correctness. -/
theorem StructuralExprCacheWF.of_cache_eq {ctx : RefCompileCtx}
    {before after : Ix.CompileM.BlockState}
    (hbefore : StructuralExprCacheWF ctx before)
    (heq : after.exprCache = before.exprCache) :
    StructuralExprCacheWF ctx after := by
  constructor <;> intro source target root h
  · exact hbefore.supported (heq ▸ h)
  · exact hbefore.sound (heq ▸ h)

/-- Caching a freshly refined supported expression preserves cache
correctness.  Digest faithfulness is used only in the collision branch of
`HashMap.insert`. -/
theorem StructuralExprCacheWF.insert {ctx : RefCompileCtx}
    {state : Ix.CompileM.BlockState} (hstate : StructuralExprCacheWF ctx state)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    {source : Ix.Expr} (hsource : StructuralExpr source)
    {target : Ixon.Expr} {root : UInt64}
    (href : compileExprRef ctx source = some target) :
    StructuralExprCacheWF ctx
      { state with exprCache := state.exprCache.insert source (target, root) } := by
  constructor
  · intro queried found foundRoot hfound
    change (state.exprCache.insert source (target, root)).get? queried =
      some (found, foundRoot) at hfound
    simp only [Std.HashMap.get?_insert] at hfound
    split at hfound
    next heq =>
      have hsame : source = queried := hfaithful hsource heq
      simpa [← hsame] using hsource
    next => exact hstate.supported hfound
  · intro queried found foundRoot hfound
    change (state.exprCache.insert source (target, root)).get? queried =
      some (found, foundRoot) at hfound
    simp only [Std.HashMap.get?_insert] at hfound
    split at hfound
    next heq =>
      have hsame : source = queried := hfaithful hsource heq
      subst queried
      have hvalue : (found, foundRoot) = (target, root) :=
        (Option.some.inj hfound).symm
      cases hvalue
      exact href
    next => exact hstate.sound hfound

/-- The pure name transition cannot affect expression memoization. -/
theorem BlockState.compileName_exprCache
    (state : Ix.CompileM.BlockState) (name : Ix.Name) :
    (state.compileName name).exprCache = state.exprCache := by
  induction name generalizing state with
  | anonymous hash =>
    rw [Ix.CompileM.BlockState.compileName.eq_1]
    split <;> rfl
  | str parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · rfl
    · exact ih _
  | num parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · rfl
    · exact ih _

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α) (next : α → Ix.CompileM.CompileM β) :
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

private theorem run_getCompileEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getCompileEnv = .ok (compileEnv, state) := by
  rfl

private theorem run_getBlockState (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getBlockState = .ok (state, state) := by
  rfl

/-- A total ordinary-compiler cache hit is a pure return. -/
theorem compileExprNoSurgeryFuel_run_cached
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (fuel : Nat) (source : Ix.Expr) (cached : Ixon.Expr × UInt64)
    (hcache : state.exprCache.get? source = some cached) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1) source) =
      .ok (cached, state) := by
  rw [Ix.CompileM.compileExprNoSurgeryFuel.eq_2,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hcache]
  rfl

private def allocState (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData) : Ix.CompileM.BlockState :=
  { state with arena := { nodes := state.arena.nodes.push node } }

private def cacheState (state : Ix.CompileM.BlockState) (source : Ix.Expr)
    (target : Ixon.Expr) (root : UInt64) : Ix.CompileM.BlockState :=
  { state with exprCache := state.exprCache.insert source (target, root) }

private theorem run_compileName (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileName name) =
      .ok ((), state.compileName name) := by
  rfl

private theorem run_allocArenaNode (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.allocArenaNode node) =
      .ok (state.arena.nodes.size.toUInt64, allocState state node) := by
  rfl

private theorem run_compileEmptyKVMap (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileKVMap #[]) = .ok (#[], state) := by
  rw [Ix.CompileM.compileKVMap, Array.mapM_empty]
  rfl

private theorem exprCompileDepth_pos (source : Ix.Expr) :
    0 < Ix.CompileM.exprCompileDepth source := by
  induction source with
  | bvar | fvar | mvar | sort | const | lit =>
    simp [Ix.CompileM.exprCompileDepth]
  | app fn arg hash ihfn iharg =>
    simp only [Ix.CompileM.exprCompileDepth]
    omega
  | lam name ty body bi hash ihty ihbody =>
    simp only [Ix.CompileM.exprCompileDepth]
    omega
  | forallE name ty body bi hash ihty ihbody =>
    simp only [Ix.CompileM.exprCompileDepth]
    omega
  | letE name ty val body nonDep hash ihty ihval ihbody =>
    simp only [Ix.CompileM.exprCompileDepth]
    omega
  | mdata data inner hash ih | proj name idx inner hash ih =>
    simp only [Ix.CompileM.exprCompileDepth]
    omega

/-- The flattened no-cache App helper refines the nested reference App tree,
provided its callback refines every supported expression within the fixed
fuel budget. -/
private theorem compileAppNoSurgery_structural_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx)
    (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      StructuralExpr source → StructuralExprCacheWF ctx state →
      compileExprRef ctx source = some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        StructuralExprCacheWF ctx state')
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAppNoSurgery
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  induction hsource generalizing state target with
  | bvar =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth StructuralExpr.bvar hstate href
  | lam hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (StructuralExpr.lam hty hbody) hstate href
  | all hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (StructuralExpr.all hty hbody) hstate href
  | letE hty hval hbody ihty ihval ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (StructuralExpr.letE hty hval hbody) hstate href
  | mdata hinner ihinner =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (StructuralExpr.mdata hinner) hstate href
  | @app fn arg hash hfn harg ihfn iharg =>
    simp [compileExprRef] at href
    rcases href with ⟨fnTarget, hfnRef, argTarget, hargRef, rfl⟩
    have hfnDepth : Ix.CompileM.exprCompileDepth fn ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hargDepth : Ix.CompileM.exprCompileDepth arg ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    obtain ⟨fnRoot, fnState, hfnRun, hfnState⟩ :=
      ihfn hfnDepth hstate hfnRef
    obtain ⟨argRoot, argState, hargRun, hargState⟩ :=
      hrecur hargDepth harg hfnState hargRef
    let root := argState.arena.nodes.size.toUInt64
    let finalState := allocState argState (.app fnRoot argRoot)
    refine ⟨root, finalState, ?_, ?_⟩
    · rw [Ix.CompileM.compileAppNoSurgery.eq_1,
        run_bind compileEnv blockEnv state _ _, hfnRun]
      simp only
      rw [run_bind compileEnv blockEnv fnState _ _, hargRun]
      simp only
      rw [run_bind compileEnv blockEnv argState _ _,
        run_allocArenaNode]
      rfl
    · exact hargState.of_cache_eq rfl

/-- One cache-miss constructor step refines the reference compiler whenever
the recursive callback does. -/
private theorem compileExprNoSurgeryStep_structural_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx) (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      StructuralExpr source → StructuralExprCacheWF ctx state →
      compileExprRef ctx source = some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        StructuralExprCacheWF ctx state')
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel + 1)
    (hsource : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  cases hsource with
  | bvar =>
    simp [compileExprRef] at href
    subst target
    let root := state.arena.nodes.size.toUInt64
    let state' := allocState state .leaf
    refine ⟨root, state', ?_, hstate.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_allocArenaNode]
    rfl
  | @app fn arg hash hfn harg =>
    simp [compileExprRef] at href
    rcases href with ⟨fnTarget, hfnRef, argTarget, hargRef, rfl⟩
    have hfnDepth : Ix.CompileM.exprCompileDepth fn ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hargDepth : Ix.CompileM.exprCompileDepth arg ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    obtain ⟨fnRoot, fnState, hfnRun, hfnState⟩ :=
      compileAppNoSurgery_structural_refines compileEnv blockEnv ctx fuel
        hrecur hfnDepth hfn hstate hfnRef
    obtain ⟨argRoot, argState, hargRun, hargState⟩ :=
      hrecur hargDepth harg hfnState hargRef
    let root := argState.arena.nodes.size.toUInt64
    let state' := allocState argState (.app fnRoot argRoot)
    refine ⟨root, state', ?_, hargState.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      Ix.CompileM.compileAppNoSurgery.eq_1,
      run_bind compileEnv blockEnv state _ _, hfnRun]
    simp only
    rw [run_bind compileEnv blockEnv fnState _ _, hargRun]
    simp only
    rw [run_bind compileEnv blockEnv argState _ _, run_allocArenaNode]
    rfl
  | @lam name ty body bi hash hty hbody =>
    simp [compileExprRef] at href
    rcases href with ⟨tyTarget, htyRef, bodyTarget, hbodyRef, rfl⟩
    have htyDepth : Ix.CompileM.exprCompileDepth ty ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hbodyDepth : Ix.CompileM.exprCompileDepth body ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    let nameState := state.compileName name
    have hnameState : StructuralExprCacheWF ctx nameState :=
      hstate.of_cache_eq (BlockState.compileName_exprCache state name)
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody htyState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let state' := allocState bodyState (.binder name.getHash bi tyRoot bodyRoot)
    refine ⟨root, state', ?_, hbodyState.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, htyRun]
    simp only
    rw [run_bind compileEnv blockEnv tyState _ _, hbodyRun]
    simp only
    rw [run_bind compileEnv blockEnv bodyState _ _, run_allocArenaNode]
    rfl
  | @all name ty body bi hash hty hbody =>
    simp [compileExprRef] at href
    rcases href with ⟨tyTarget, htyRef, bodyTarget, hbodyRef, rfl⟩
    have htyDepth : Ix.CompileM.exprCompileDepth ty ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hbodyDepth : Ix.CompileM.exprCompileDepth body ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    let nameState := state.compileName name
    have hnameState : StructuralExprCacheWF ctx nameState :=
      hstate.of_cache_eq (BlockState.compileName_exprCache state name)
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody htyState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let state' := allocState bodyState (.binder name.getHash bi tyRoot bodyRoot)
    refine ⟨root, state', ?_, hbodyState.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, htyRun]
    simp only
    rw [run_bind compileEnv blockEnv tyState _ _, hbodyRun]
    simp only
    rw [run_bind compileEnv blockEnv bodyState _ _, run_allocArenaNode]
    rfl
  | @letE name ty val body nonDep hash hty hval hbody =>
    simp [compileExprRef] at href
    rcases href with
      ⟨tyTarget, htyRef, valTarget, hvalRef, bodyTarget, hbodyRef, rfl⟩
    have htyDepth : Ix.CompileM.exprCompileDepth ty ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hvalDepth : Ix.CompileM.exprCompileDepth val ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hbodyDepth : Ix.CompileM.exprCompileDepth body ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    let nameState := state.compileName name
    have hnameState : StructuralExprCacheWF ctx nameState :=
      hstate.of_cache_eq (BlockState.compileName_exprCache state name)
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨valRoot, valState, hvalRun, hvalState⟩ :=
      hrecur hvalDepth hval htyState hvalRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody hvalState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let state' := allocState bodyState
      (.letBinder name.getHash tyRoot valRoot bodyRoot)
    refine ⟨root, state', ?_, hbodyState.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, htyRun]
    simp only
    rw [run_bind compileEnv blockEnv tyState _ _, hvalRun]
    simp only
    rw [run_bind compileEnv blockEnv valState _ _, hbodyRun]
    simp only
    rw [run_bind compileEnv blockEnv bodyState _ _, run_allocArenaNode]
    rfl
  | @mdata inner hash hinner =>
    have hinnerRef : compileExprRef ctx inner = some target := by
      simpa [compileExprRef] using href
    have hinnerDepth : Ix.CompileM.exprCompileDepth inner ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    obtain ⟨innerRoot, innerState, hinnerRun, hinnerState⟩ :=
      hrecur hinnerDepth hinner hstate hinnerRef
    let root := innerState.arena.nodes.size.toUInt64
    let state' := allocState innerState (.mdata #[#[]] innerRoot)
    refine ⟨root, state', ?_, hinnerState.of_cache_eq (by rfl)⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_compileEmptyKVMap]
    simp only
    rw [run_bind compileEnv blockEnv state _ _, hinnerRun]
    simp only
    rw [run_bind compileEnv blockEnv innerState _ _, run_allocArenaNode]
    rfl

/-- Exact miss transition for the structural leaf. -/
theorem compileExprNoSurgeryFuel_run_bvar_miss
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (fuel idx : Nat) (hash : Address)
    (hmissing : state.exprCache.get? (.bvar idx hash) = none) :
    let root := state.arena.nodes.size.toUInt64
    let state' := cacheState (allocState state .leaf) (.bvar idx hash)
      (.var idx.toUInt64) root
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1) (.bvar idx hash)) =
      .ok ((.var idx.toUInt64, root), state') := by
  rw [Ix.CompileM.compileExprNoSurgeryFuel.eq_2,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing]
  rfl

/-- Production compilation refines the reference compiler for a bound
variable, including arbitrary sound warm expression caches. -/
theorem compileExprNoSurgeryFuel_bvar_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    (state : Ix.CompileM.BlockState) (hstate : StructuralExprCacheWF ctx state)
    (fuel idx : Nat) (hash : Address) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.bvar idx hash)) =
        .ok ((.var idx.toUInt64, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  cases hlookup : state.exprCache.get? (.bvar idx hash) with
  | some cached =>
    rcases cached with ⟨cachedTarget, cachedRoot⟩
    have hsound := hstate.sound hlookup
    simp [compileExprRef] at hsound
    subst cachedTarget
    exact ⟨cachedRoot, state,
      compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
        (.bvar idx hash) (.var idx.toUInt64, cachedRoot) hlookup,
      hstate⟩
  | none =>
    let root := state.arena.nodes.size.toUInt64
    let allocated := allocState state .leaf
    let state' := cacheState allocated (.bvar idx hash)
      (.var idx.toUInt64) root
    refine ⟨root, state',
      compileExprNoSurgeryFuel_run_bvar_miss compileEnv blockEnv state fuel idx
        hash hlookup, ?_⟩
    apply StructuralExprCacheWF.insert
      (hstate.of_cache_eq (by rfl)) hfaithful StructuralExpr.bvar
    rfl

/-- The fuel-total ordinary compiler refines `compileExprRef` on the complete
recursive structural fragment and preserves a sound warm expression cache. -/
theorem compileExprNoSurgeryFuel_structural_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    {fuel : Nat} {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  induction fuel generalizing state source target with
  | zero =>
    have hpos := exprCompileDepth_pos source
    omega
  | succ fuel ih =>
    cases hlookup : state.exprCache.get? source with
    | some cached =>
      rcases cached with ⟨cachedTarget, cachedRoot⟩
      have hcachedRef := hstate.sound hlookup
      have htarget : cachedTarget = target :=
        Option.some.inj (hcachedRef.symm.trans href)
      subst cachedTarget
      exact ⟨cachedRoot, state,
        compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
          source (target, cachedRoot) hlookup,
        hstate⟩
    | none =>
      obtain ⟨root, stepState, hstepRun, hstepState⟩ :=
        compileExprNoSurgeryStep_structural_refines compileEnv blockEnv ctx
          fuel (fun hdepth hsource hstate href =>
            ih hdepth hsource hstate href)
          hdepth hsource hstate href
      let finalState := cacheState stepState source target root
      refine ⟨root, finalState, ?_, ?_⟩
      · rw [Ix.CompileM.compileExprNoSurgeryFuel.eq_2,
          run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
          run_getBlockState]
        simp only
        rw [hlookup]
        change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
          let (result, resultRoot) ← Ix.CompileM.compileExprNoSurgeryStep
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source
          Ix.CompileM.modifyBlockState fun current =>
            { current with
              exprCache := current.exprCache.insert source (result, resultRoot) }
          pure (result, resultRoot)) = _
        rw [run_bind compileEnv blockEnv state _ _, hstepRun]
        rfl
      · simpa [finalState, cacheState] using
          hstepState.insert hfaithful hsource href

/-- The public total ordinary entry point refines the reference compiler on
the structural fragment. -/
theorem compileExprNoSurgery_run_structural_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} (hsource : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgery source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  exact compileExprNoSurgeryFuel_structural_refines compileEnv blockEnv ctx
    hfaithful (Nat.le_refl _) hsource hstate href

/-- In a globally surgery-free environment, the actual production
`compileExpr` entry point refines the total reference compiler on the
structural fragment. -/
theorem compileExpr_run_structural_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (ctx : RefCompileCtx)
    (hfree : compileEnv.surgeryFree = true)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} (hsource : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgery_run_structural_refines compileEnv blockEnv ctx
      hfaithful hsource hstate href
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  exact hrun

/-- The production result in the structural fragment therefore denotes the
same independent Lean4Lean value as its named Ix source. -/
theorem compileExpr_run_structural_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {ctx : RefCompileCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (hfree : compileEnv.surgeryFree = true)
    (hfaithful : ExprKeyFaithfulOn StructuralExpr)
    (hctx : RefCompileCtxRel ctx sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} {value : Lean4Lean.VExpr}
    (hstruct : StructuralExpr source)
    (hstate : StructuralExprCacheWF ctx state)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals source value)
    (href : compileExprRef ctx source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      StructuralExprCacheWF ctx state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals target value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_structural_refines compileEnv blockEnv ctx hfree hfaithful
      hstruct hstate href
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

/-- The public production dispatcher selects the total ordinary compiler in
a globally surgery-free environment. -/
theorem compileExpr_run_surgeryFree
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Expr) (hfree : compileEnv.surgeryFree = true) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileExpr source) =
      Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileExprNoSurgery source) := by
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp [hfree]

end Ix.Compile.Verify
