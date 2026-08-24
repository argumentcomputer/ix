import Ix.Compile.Verify.CompileUniv
import Ix.Compile.Verify.Arena
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
premise.

The second layer fixes a completed preseed snapshot and relates its universe,
reference, and name-resolution tables to a concrete `RefCompileCtx`.  It
closes the complete ordinary-expression tree: sorts, arbitrary-universe local
and external constants, recursive projections, literals, structural
composition, and supported scalar metadata maps.  The proof covers warm
caches, universe spelling patches, blob/name commits, and independent
Lean4Lean values. Its strengthened frontier also relates the returned
`UInt64` root, including the encoded KV map, to the append-only presentation
arena under an explicit no-wrap capacity premise.
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

/-- The reference compiler's choices frozen at the completed preseed state
for one ordinary-expression run.  The production compiler may grow metadata,
memo, blob, and arena fields after this snapshot, but its primary universe
and reference tables and its block-local resolution maps must retain this
view. -/
def frozenRefCompileCtx (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) : RefCompileCtx :=
  { univIndex := fun level => do
      let raw ← compileUnivRef (univParamIndex blockEnv.univCtx) level
      snapshot.univsIndex.get? (Ixon.canonUniv raw)
    refIndex := fun name => do
      let addr ← resolveConstAddr? compileEnv snapshot name
      snapshot.refsIndex.get? addr
    mutIndex := fun name =>
      (blockEnv.mutCtx.get? name).map Nat.toUInt64
    literalRef := fun literal =>
      snapshot.refsIndex.get? (literalAddress literal) }

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

/-- The complete ordinary syntax accepted by the no-surgery compiler, with
metadata restricted to values handled by the total scalar reference
serializer. -/
inductive OrdinaryExpr : Ix.Expr → Prop where
  | bvar {idx hash} : OrdinaryExpr (.bvar idx hash)
  | sort {level hash} : OrdinaryExpr (.sort level hash)
  | const {name levels hash} : OrdinaryExpr (.const name levels hash)
  | app {fn arg hash} : OrdinaryExpr fn → OrdinaryExpr arg →
      OrdinaryExpr (.app fn arg hash)
  | lam {name ty body bi hash} : OrdinaryExpr ty → OrdinaryExpr body →
      OrdinaryExpr (.lam name ty body bi hash)
  | all {name ty body bi hash} : OrdinaryExpr ty → OrdinaryExpr body →
      OrdinaryExpr (.forallE name ty body bi hash)
  | letE {name ty val body nonDep hash} :
      OrdinaryExpr ty → OrdinaryExpr val → OrdinaryExpr body →
      OrdinaryExpr (.letE name ty val body nonDep hash)
  | lit {literal hash} : OrdinaryExpr (.lit literal hash)
  | proj {typeName field val hash} : OrdinaryExpr val →
      OrdinaryExpr (.proj typeName field val hash)
  | mdata {data inner hash} : KVMapSupported data → OrdinaryExpr inner →
      OrdinaryExpr (.mdata data inner hash)

theorem StructuralExpr.ordinary {source : Ix.Expr} :
    StructuralExpr source → OrdinaryExpr source
  | .bvar => .bvar
  | .app hfn harg => .app hfn.ordinary harg.ordinary
  | .lam hty hbody => .lam hty.ordinary hbody.ordinary
  | .all hty hbody => .all hty.ordinary hbody.ordinary
  | .letE hty hval hbody =>
    .letE hty.ordinary hval.ordinary hbody.ordinary
  | .mdata hinner => .mdata KVMapSupported.empty hinner.ordinary

/-- Ordinary syntax paired with the exact finite universe support needed by
production `compileUniv`.  This is the recursive source domain of the frozen
ordinary-expression theorem. -/
inductive SupportedOrdinaryExpr (levelSupport : Ix.Level → Prop) :
    Ix.Expr → Prop where
  | bvar {idx hash} : SupportedOrdinaryExpr levelSupport (.bvar idx hash)
  | sort {level hash} : levelSupport level →
      SupportedOrdinaryExpr levelSupport (.sort level hash)
  | const {name levels hash} :
      (∀ level ∈ levels, levelSupport level) →
      SupportedOrdinaryExpr levelSupport (.const name levels hash)
  | app {fn arg hash} : SupportedOrdinaryExpr levelSupport fn →
      SupportedOrdinaryExpr levelSupport arg →
      SupportedOrdinaryExpr levelSupport (.app fn arg hash)
  | lam {name ty body bi hash} : SupportedOrdinaryExpr levelSupport ty →
      SupportedOrdinaryExpr levelSupport body →
      SupportedOrdinaryExpr levelSupport (.lam name ty body bi hash)
  | all {name ty body bi hash} : SupportedOrdinaryExpr levelSupport ty →
      SupportedOrdinaryExpr levelSupport body →
      SupportedOrdinaryExpr levelSupport (.forallE name ty body bi hash)
  | letE {name ty val body nonDep hash} :
      SupportedOrdinaryExpr levelSupport ty →
      SupportedOrdinaryExpr levelSupport val →
      SupportedOrdinaryExpr levelSupport body →
      SupportedOrdinaryExpr levelSupport (.letE name ty val body nonDep hash)
  | lit {literal hash} :
      SupportedOrdinaryExpr levelSupport (.lit literal hash)
  | proj {typeName field val hash} : SupportedOrdinaryExpr levelSupport val →
      SupportedOrdinaryExpr levelSupport (.proj typeName field val hash)
  | mdata {data inner hash} : KVMapSupported data →
      SupportedOrdinaryExpr levelSupport inner →
      SupportedOrdinaryExpr levelSupport (.mdata data inner hash)

theorem SupportedOrdinaryExpr.ordinary {levelSupport : Ix.Level → Prop}
    {source : Ix.Expr} :
    SupportedOrdinaryExpr levelSupport source → OrdinaryExpr source
  | .bvar => .bvar
  | .sort _ => .sort
  | .const _ => .const
  | .app hfn harg => .app hfn.ordinary harg.ordinary
  | .lam hty hbody => .lam hty.ordinary hbody.ordinary
  | .all hty hbody => .all hty.ordinary hbody.ordinary
  | .letE hty hval hbody =>
    .letE hty.ordinary hval.ordinary hbody.ordinary
  | .lit => .lit
  | .proj hval => .proj hval.ordinary
  | .mdata hdata hinner => .mdata hdata hinner.ordinary

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

/-- A warm production expression cache for the complete ordinary syntax.
The support component isolates digest faithfulness from semantic soundness;
the latter always refers to the single frozen reference context. -/
structure OrdinaryExprCacheWF (ctx : RefCompileCtx)
    (state : Ix.CompileM.BlockState) : Prop where
  supported : ∀ {source target root},
    state.exprCache.get? source = some (target, root) → OrdinaryExpr source
  sound : ∀ {source target root},
    state.exprCache.get? source = some (target, root) →
      compileExprRef ctx source = some target

theorem OrdinaryExprCacheWF.empty (ctx : RefCompileCtx) :
    OrdinaryExprCacheWF ctx (default : Ix.CompileM.BlockState) := by
  constructor <;> intro source target root h
  · change ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64)).get? source =
      some (target, root) at h
    simp at h
  · change ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64)).get? source =
      some (target, root) at h
    simp at h

theorem OrdinaryExprCacheWF.of_cache_eq {ctx : RefCompileCtx}
    {before after : Ix.CompileM.BlockState}
    (hbefore : OrdinaryExprCacheWF ctx before)
    (heq : after.exprCache = before.exprCache) :
    OrdinaryExprCacheWF ctx after := by
  constructor <;> intro source target root h
  · exact hbefore.supported (heq ▸ h)
  · exact hbefore.sound (heq ▸ h)

theorem OrdinaryExprCacheWF.insert {ctx : RefCompileCtx}
    {state : Ix.CompileM.BlockState} (hstate : OrdinaryExprCacheWF ctx state)
    (hfaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr} (hsource : OrdinaryExpr source)
    {target : Ixon.Expr} {root : UInt64}
    (href : compileExprRef ctx source = some target) :
    OrdinaryExprCacheWF ctx
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

/-- Inserting a newly allocated ordinary-expression root preserves arena
cache soundness. Digest faithfulness is needed only when the physical hash
map reports that the new key replaces the queried key. -/
theorem ArenaCacheWF.insert {state : Ix.CompileM.BlockState}
    (hstate : ArenaCacheWF state)
    (hfaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr} (hsource : OrdinaryExpr source)
    {target : Ixon.Expr} {root : UInt64}
    (hroot : ArenaRel source root state.arena) :
    ArenaCacheWF
      { state with exprCache := state.exprCache.insert source (target, root) } := by
  constructor
  intro queried found foundRoot hfound
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
    exact hroot
  next => exact hstate.sound hfound

/-- All mutable invariants needed by table-backed ordinary-expression
compilation.  `snapshot` fixes the reference compiler, while `tables` states
that the live production state still exposes exactly that preseed view. -/
structure FrozenExprStateWF (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (snapshot state : Ix.CompileM.BlockState) : Prop where
  tables : exprTableView state = exprTableView snapshot
  exprCache : OrdinaryExprCacheWF
    (frozenRefCompileCtx compileEnv blockEnv snapshot) state
  univCache : UnivCacheWF (univParamIndex blockEnv.univCtx) levelSupport state
  canonUnivCache : CanonUnivCacheWF state

theorem FrozenExprStateWF.of_frame
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot before after : Ix.CompileM.BlockState}
    (hbefore : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot before)
    (htables : exprTableView after = exprTableView before)
    (hexprCache : after.exprCache = before.exprCache)
    (hunivCache : after.univCache = before.univCache)
    (hcanonCache : after.canonUnivCache = before.canonUnivCache) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot after :=
  { tables := htables.trans hbefore.tables
    exprCache := hbefore.exprCache.of_cache_eq hexprCache
    univCache := hbefore.univCache.of_cache_eq hunivCache
    canonUnivCache := hbefore.canonUnivCache.of_cache_eq hcanonCache }

/-- Scalar metadata compilation preserves the full frozen expression state. -/
theorem FrozenExprStateWF.of_metaFrame
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot before after : Ix.CompileM.BlockState}
    (hbefore : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot before)
    (hframe : MetaStateFrame before after) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot after :=
  hbefore.of_frame hframe.tables hframe.exprCache hframe.univCache
    hframe.canonUnivCache

/-- Scalar metadata compilation also preserves every warm arena-cache root. -/
theorem ArenaCacheWF.of_metaFrame {before after : Ix.CompileM.BlockState}
    (hbefore : ArenaCacheWF before) (hframe : MetaStateFrame before after) :
    ArenaCacheWF after :=
  hbefore.of_frame hframe.exprCache (by
    rw [hframe.arena]
    exact ArenaExtends.refl before.arena)

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

/-- Name serialization never changes the current expression metadata arena. -/
theorem BlockState.compileName_arena
    (state : Ix.CompileM.BlockState) (name : Ix.Name) :
    (state.compileName name).arena = state.arena := by
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

/-- Name serialization changes only presentation-side name/blob stores, so
all fields used by the frozen ordinary-expression relation are unchanged. -/
theorem BlockState.compileName_frozenFrame
    (state : Ix.CompileM.BlockState) (name : Ix.Name) :
    exprTableView (state.compileName name) = exprTableView state ∧
      (state.compileName name).exprCache = state.exprCache ∧
      (state.compileName name).univCache = state.univCache ∧
      (state.compileName name).canonUnivCache = state.canonUnivCache := by
  induction name generalizing state with
  | anonymous hash =>
    rw [Ix.CompileM.BlockState.compileName.eq_1]
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | str parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ih _
  | num parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ih _

private theorem FrozenExprStateWF.compileName
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (name : Ix.Name) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (state.compileName name) := by
  have hframe := BlockState.compileName_frozenFrame state name
  exact hstate.of_frame hframe.1 hframe.2.1 hframe.2.2.1 hframe.2.2.2

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

private theorem run_getBlockEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getBlockEnv = .ok (blockEnv, state) := by
  rfl

private theorem run_getBlockState (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getBlockState = .ok (state, state) := by
  rfl

private theorem run_pure (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (value : α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (pure value) =
      .ok (value, state) := by
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

private def patchState (state : Ix.CompileM.BlockState) (root : UInt64)
    (indices : Array UInt64) : Ix.CompileM.BlockState :=
  { state with
    univPatches := state.univPatches.push
      { arenaIdx := root, univIdxs := indices } }

private def blobState (state : Ix.CompileM.BlockState) (addr : Address)
    (bytes : ByteArray) : Ix.CompileM.BlockState :=
  { state with blockBlobs := state.blockBlobs.insert addr bytes }

/-- The Ixon leaf selected by a source literal once its committed blob address
has been resolved in the frozen reference table. -/
def literalExpr (literal : Lean.Literal) (idx : UInt64) : Ixon.Expr :=
  match literal with
  | .natVal _ => .nat idx
  | .strVal _ => .str idx

private theorem allocState_arenaExtends (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData) :
    ArenaExtends state.arena (allocState state node).arena := by
  exact ArenaExtends.push state.arena node

private theorem allocState_root (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData)
    (hroom : state.arena.nodes.size < UInt64.size) :
    (allocState state node).arena.nodes[
        state.arena.nodes.size.toUInt64.toNat]? = some node := by
  have hidx : state.arena.nodes.size.toUInt64.toNat =
      state.arena.nodes.size :=
    UInt64.toNat_ofNat_of_lt hroom
  simp [allocState, hidx]

private theorem allocState_size (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData) :
    (allocState state node).arena.nodes.size = state.arena.nodes.size + 1 := by
  simp [allocState]

/-- A state-only prelude followed by one arena allocation preserves all warm
cache roots and returns the newly appended node at its `UInt64` index. -/
private theorem arenaLeafFrame
    {before middle : Ix.CompileM.BlockState}
    (hcache : ArenaCacheWF before)
    (hcacheEq : middle.exprCache = before.exprCache)
    (harenaEq : middle.arena = before.arena)
    (node : Ixon.ExprMetaData)
    (hroom : before.arena.nodes.size + 1 < UInt64.size) :
    let root := middle.arena.nodes.size.toUInt64
    let after := allocState middle node
    ArenaCacheWF after ∧
      ArenaExtends before.arena after.arena ∧
      after.arena.nodes.size ≤ before.arena.nodes.size + 1 ∧
      after.arena.nodes[root.toNat]? = some node := by
  let root := middle.arena.nodes.size.toUInt64
  let after := allocState middle node
  have hmiddleExtends : ArenaExtends before.arena middle.arena := by
    rw [harenaEq]
    exact ArenaExtends.refl before.arena
  have hallocExtends : ArenaExtends middle.arena after.arena := by
    dsimp [after]
    exact allocState_arenaExtends middle node
  have hmiddleRoom : middle.arena.nodes.size < UInt64.size := by
    rw [harenaEq]
    omega
  have hroot : after.arena.nodes[root.toNat]? = some node := by
    simpa [after, root] using allocState_root middle node hmiddleRoom
  have hafterCache : ArenaCacheWF after :=
    hcache.of_frame (by simpa [after, allocState] using hcacheEq)
      (ArenaExtends.trans hmiddleExtends hallocExtends)
  refine ⟨hafterCache,
    ArenaExtends.trans hmiddleExtends hallocExtends, ?_, hroot⟩
  simp [allocState, harenaEq]

private theorem FrozenExprStateWF.alloc
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (node : Ixon.ExprMetaData) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (allocState state node) := by
  exact hstate.of_frame rfl rfl rfl rfl

private theorem FrozenExprStateWF.patch
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (root : UInt64) (indices : Array UInt64) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (patchState state root indices) := by
  exact hstate.of_frame rfl rfl rfl rfl

private theorem FrozenExprStateWF.blob
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (addr : Address) (bytes : ByteArray) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (blobState state addr bytes) := by
  exact hstate.of_frame rfl rfl rfl rfl

private theorem FrozenExprStateWF.cache
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {snapshot state : Ix.CompileM.BlockState}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hfaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr} (hsource : OrdinaryExpr source)
    {target : Ixon.Expr} {root : UInt64}
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
      (cacheState state source target root) := by
  refine
    { tables := hstate.tables
      exprCache := ?_
      univCache := hstate.univCache.of_cache_eq rfl
      canonUnivCache := hstate.canonUnivCache.of_cache_eq rfl }
  simpa [cacheState] using
    hstate.exprCache.insert hfaithful hsource href

private theorem run_compileName (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileName name) =
      .ok ((), state.compileName name) := by
  rfl

private theorem run_lookupConstAddr_resolved
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) (addr : Address)
    (hresolve : resolveConstAddr? compileEnv state name = some addr) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.lookupConstAddr name) = .ok (addr, state) := by
  rw [Ix.CompileM.lookupConstAddr,
    run_bind compileEnv blockEnv state Ix.CompileM.getCompileEnv,
    run_getCompileEnv]
  simp only
  rw [run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
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
      cases haux : state.auxNameToAddr.get? name with
      | some found =>
        simp only [haux, Option.some.injEq] at hresolve
        subst found
        simp only
        rfl
      | none =>
        simp only [haux] at hresolve
        simp only
        change compileEnv.auxNameToAddr.get? name = some addr at hresolve
        rw [hresolve]
        rfl

private theorem run_internRef_hit (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (addr : Address) (idx : UInt64)
    (hindex : state.refsIndex.get? addr = some idx) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internRef addr) = .ok (idx, state) := by
  change Except.ok ((state.internRef addr).2, (state.internRef addr).1) =
    Except.ok (idx, state)
  rw [Ix.CompileM.BlockState.internRef, hindex]

private theorem run_allocArenaNode (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (node : Ixon.ExprMetaData) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.allocArenaNode node) =
      .ok (state.arena.nodes.size.toUInt64, allocState state node) := by
  rfl

private theorem run_pushUnivPatch (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (root : UInt64) (indices : Array UInt64) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.pushUnivPatch root indices) =
      .ok ((), patchState state root indices) := by
  rfl

private theorem run_insertBlockBlob (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (addr : Address) (bytes : ByteArray) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.modifyBlockState fun current =>
          { current with
            blockBlobs := current.blockBlobs.insert addr bytes }) =
      .ok ((), blobState state addr bytes) := by
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

/-- Lift an exact ordinary leaf step through the production cache protocol.
The helper is shared by table-backed constructors whose recursive callback is
unused at the current leaf. -/
private theorem compileExprNoSurgeryFuel_leaf_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr} {target : Ixon.Expr}
    (hsource : OrdinaryExpr source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target)
    (fuel : Nat)
    (hstep : ∃ root stepState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), stepState) ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot stepState) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1) source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  cases hlookup : state.exprCache.get? source with
  | some cached =>
    rcases cached with ⟨cachedTarget, cachedRoot⟩
    have hcached := hstate.exprCache.sound hlookup
    have htarget : cachedTarget = target :=
      Option.some.inj (hcached.symm.trans href)
    subst cachedTarget
    exact ⟨cachedRoot, state,
      compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
        source (target, cachedRoot) hlookup,
      hstate⟩
  | none =>
    obtain ⟨root, stepState, hstepRun, hstepState⟩ := hstep
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
    · exact hstepState.cache hexprFaithful hsource href

/-- The table-backed `.sort` constructor performs the proved canonical
universe transition, allocates its leaf metadata root, and records an
original-spelling patch exactly when canonicalization changed the source
universe.  All frozen-table and memo invariants survive the step. -/
theorem compileExprNoSurgeryStep_sort_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {raw : Ixon.Univ} {idx : UInt64} (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hindex : state.univsIndex.get? (Ixon.canonUniv raw) = some idx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨original?, univState, hunivRun, hunivState, hcanonState,
      hview, hexprCache, _⟩ :=
    compileAndInternUnivCanon_run_refines compileEnv blockEnv hclosed
      hlevelFaithful hlevel hstate.univCache hstate.canonUnivCache hraw hindex
  have hfrozenUniv :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot univState :=
    { tables := hview.trans hstate.tables
      exprCache := hstate.exprCache.of_cache_eq hexprCache
      univCache := hunivState
      canonUnivCache := hcanonState }
  let root := univState.arena.nodes.size.toUInt64
  let allocated := allocState univState .leaf
  have hfrozenAllocated :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot allocated :=
    hfrozenUniv.alloc .leaf
  cases original? with
  | none =>
    refine ⟨root, allocated, ?_, hfrozenAllocated⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, hunivRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_allocArenaNode]
    rfl
  | some original =>
    let finalState := patchState allocated root #[original]
    refine ⟨root, finalState, ?_, hfrozenAllocated.patch root #[original]⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, hunivRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_allocArenaNode]
    simp only
    rw [run_bind compileEnv blockEnv allocated _ _, run_pushUnivPatch]
    rfl

/-- The fuel-total ordinary compiler refines the frozen reference decision
for a sort, for both sound warm-cache hits and production cache misses. -/
theorem compileExprNoSurgeryFuel_sort_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {raw : Ixon.Univ} {idx : UInt64} (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hindex : state.univsIndex.get? (Ixon.canonUniv raw) = some idx)
    (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmaps := congrArg ExprTableView.univsIndex hstate.tables
  change state.univsIndex = snapshot.univsIndex at hmaps
  have hsnapshotIndex :
      snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
    rw [← hmaps]
    exact hindex
  have hctxIndex :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex level =
        some idx := by
    simp only [frozenRefCompileCtx]
    rw [hraw]
    change snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx
    exact hsnapshotIndex
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.sort level hash) = some (.sort idx) := by
    simp [compileExprRef, hctxIndex]
  cases hlookup : state.exprCache.get? (.sort level hash) with
  | some cached =>
    rcases cached with ⟨cachedTarget, cachedRoot⟩
    have hcached := hstate.exprCache.sound hlookup
    have htarget : cachedTarget = .sort idx :=
      Option.some.inj (hcached.symm.trans href)
    subst cachedTarget
    exact ⟨cachedRoot, state,
      compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
        (.sort level hash) (.sort idx, cachedRoot) hlookup,
      hstate⟩
  | none =>
    obtain ⟨root, stepState, hstepRun, hstepState⟩ :=
      compileExprNoSurgeryStep_sort_refines compileEnv blockEnv snapshot
        hclosed hlevelFaithful
        (Ix.CompileM.compileExprNoSurgeryFuel fuel) hlevel hstate hraw hindex
    let finalState := cacheState stepState (.sort level hash) (.sort idx) root
    refine ⟨root, finalState, ?_, ?_⟩
    · rw [Ix.CompileM.compileExprNoSurgeryFuel.eq_2,
        run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
        run_getBlockState]
      simp only
      rw [hlookup]
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        let (result, resultRoot) ← Ix.CompileM.compileExprNoSurgeryStep
          (Ix.CompileM.compileExprNoSurgeryFuel fuel) (.sort level hash)
        Ix.CompileM.modifyBlockState fun current =>
          { current with
            exprCache := current.exprCache.insert
              (.sort level hash) (result, resultRoot) }
        pure (result, resultRoot)) = _
      rw [run_bind compileEnv blockEnv state _ _, hstepRun]
      rfl
    · exact hstepState.cache hexprFaithful OrdinaryExpr.sort href

/-- The public total no-surgery entry point compiles a sort to the canonical
preseed index selected by its frozen reference context. -/
theorem compileExprNoSurgery_run_sort_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {raw : Ixon.Univ} {idx : UInt64} (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hpreseed : snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgery (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmaps := congrArg ExprTableView.univsIndex hstate.tables
  change state.univsIndex = snapshot.univsIndex at hmaps
  have hindex :
      state.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
    rw [hmaps]
    exact hpreseed
  simpa [Ix.CompileM.compileExprNoSurgery, Ix.CompileM.exprCompileDepth] using
    compileExprNoSurgeryFuel_sort_refines compileEnv blockEnv snapshot hclosed
      hlevelFaithful hexprFaithful hlevel hstate hraw hindex 0

/-- In a surgery-free environment, the actual production dispatcher has the
same canonical-preseed sort refinement. -/
theorem compileExpr_run_sort_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {raw : Ixon.Univ} {idx : UInt64} (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hpreseed : snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgery_run_sort_refines compileEnv blockEnv snapshot hclosed
      hlevelFaithful hexprFaithful hlevel hstate hraw hpreseed
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  exact hrun

/-- The production sort result therefore denotes the same independent
Lean4Lean value as the source sort. -/
theorem compileExpr_run_sort_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {raw : Ixon.Univ} {idx : UInt64} {value : Lean4Lean.VExpr}
    (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hpreseed : snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals
      (.sort level hash) value) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        (.sort idx) value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_sort_refines compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hlevel hstate hraw hpreseed
  have hctxIndex :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex level =
        some idx := by
    simp only [frozenRefCompileCtx]
    rw [hraw]
    change snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.sort level hash) = some (.sort idx) := by
    simp [compileExprRef, hctxIndex]
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

/-- One frozen reference-context universe decision is implemented by the
complete production canonicalization/interning transition. -/
theorem FrozenExprStateWF.compileAndInternUnivCanon_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {idx : UInt64}
    (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hctxIndex :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex level =
        some idx) :
    ∃ original? state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAndInternUnivCanon level) =
        .ok ((idx, original?), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      state'.arena = state.arena ∧
      state'.exprCache = state.exprCache := by
  cases hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level with
  | none =>
    simp [frozenRefCompileCtx, hraw] at hctxIndex
  | some raw =>
    have hctxIndex' := hctxIndex
    simp only [frozenRefCompileCtx] at hctxIndex'
    rw [hraw] at hctxIndex'
    have hpreseed :
        snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
      change snapshot.univsIndex[Ixon.canonUniv raw]? = some idx at hctxIndex'
      change snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx
      exact hctxIndex'
    have hmaps := univsIndex_eq_of_exprTableView_eq hstate.tables
    have hindex :
        state.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
      rw [hmaps]
      exact hpreseed
    obtain ⟨original?, state', hrun, huniv, hcanon, hview, hexpr,
        harena⟩ :=
      compileAndInternUnivCanon_run_refines compileEnv blockEnv hclosed
        hlevelFaithful hlevel hstate.univCache hstate.canonUnivCache hraw
        hindex
    exact ⟨original?, state', hrun,
      { tables := hview.trans hstate.tables
        exprCache := hstate.exprCache.of_cache_eq hexpr
        univCache := huniv
        canonUnivCache := hcanon }, harena, hexpr⟩

private theorem compileExprNoSurgeryStep_sort_ctx_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {level : Ix.Level} {hash : Address}
    {idx : UInt64} (hlevel : levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hctxIndex :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex level =
        some idx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile (.sort level hash)) =
        .ok ((.sort idx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  cases hraw : compileUnivRef (univParamIndex blockEnv.univCtx) level with
  | none => simp [frozenRefCompileCtx, hraw] at hctxIndex
  | some raw =>
    have hctxIndex' := hctxIndex
    simp only [frozenRefCompileCtx] at hctxIndex'
    rw [hraw] at hctxIndex'
    have hpreseed :
        snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
      change snapshot.univsIndex[Ixon.canonUniv raw]? = some idx at hctxIndex'
      change snapshot.univsIndex.get? (Ixon.canonUniv raw) = some idx
      exact hctxIndex'
    have hmaps := univsIndex_eq_of_exprTableView_eq hstate.tables
    have hindex : state.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
      rw [hmaps]
      exact hpreseed
    exact compileExprNoSurgeryStep_sort_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful compile hlevel hstate hraw hindex

/-- Left-to-right production compilation of a list of universe arguments
implements the frozen reference indices and preserves the live state
relation.  The optional second component retains source spellings for the
constant occurrence's metadata patch. -/
private theorem compileAndInternUnivCanon_list_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    {state : Ix.CompileM.BlockState} {levels : List Ix.Level}
    {indices : List UInt64}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices) :
    ∃ compiled state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (levels.mapM Ix.CompileM.compileAndInternUnivCanon) =
        .ok (compiled, state') ∧
      compiled.map Prod.fst = indices ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      state'.arena = state.arena ∧
      state'.exprCache = state.exprCache := by
  induction levels generalizing state indices with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at href
    subst indices
    exact ⟨[], state, run_pure compileEnv blockEnv state [], rfl, hstate,
      rfl, rfl⟩
  | cons level levels ih =>
    cases hhead :
        (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex level with
    | none => simp [List.mapM_cons, hhead] at href
    | some idx =>
      cases htail : levels.mapM
          (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex with
      | none => simp [List.mapM_cons, hhead, htail] at href
      | some tailIndices =>
        have hindices : indices = idx :: tailIndices := by
          simpa [List.mapM_cons, hhead, htail] using href.symm
        subst indices
        have hlevel : levelSupport level := hlevels level (by simp)
        have htailLevels : ∀ child ∈ levels, levelSupport child := by
          intro child hmem
          exact hlevels child (by simp [hmem])
        obtain ⟨original?, headState, hheadRun, hheadState, hheadArena,
            hheadCache⟩ :=
          hstate.compileAndInternUnivCanon_refines compileEnv blockEnv snapshot
            hclosed hlevelFaithful hlevel hhead
        obtain ⟨tailCompiled, finalState, htailRun, htailMap,
            hfinalState, htailArena, htailCache⟩ :=
          ih htailLevels hheadState htail
        refine ⟨(idx, original?) :: tailCompiled, finalState, ?_, ?_,
          hfinalState, htailArena.trans hheadArena,
          htailCache.trans hheadCache⟩
        · rw [List.mapM_cons,
            run_bind compileEnv blockEnv state _ _, hheadRun]
          simp only
          rw [run_bind compileEnv blockEnv headState _ _, htailRun]
          rfl
        · simp [htailMap]

/-- Array form used verbatim by production constant compilation. -/
theorem compileAndInternUnivCanon_array_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    {state : Ix.CompileM.BlockState} {levels : Array Ix.Level}
    {indices : Array UInt64}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices) :
    ∃ compiled state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (levels.mapM Ix.CompileM.compileAndInternUnivCanon) =
        .ok (compiled, state') ∧
      compiled.map Prod.fst = indices ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      state'.arena = state.arena ∧
      state'.exprCache = state.exprCache := by
  have hlevelsList : ∀ level ∈ levels.toList, levelSupport level := by
    intro level hmem
    exact hlevels level (by simpa using hmem)
  have hrefList :
      levels.toList.mapM
          (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices.toList := by
    have hmapped := congrArg (Option.map Array.toList) href
    change Array.toList <$> levels.mapM
        (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
      Option.map Array.toList (some indices) at hmapped
    rw [Array.toList_mapM] at hmapped
    simpa using hmapped
  obtain ⟨compiled, state', hrun, hmap, hstate', harena, hcache⟩ :=
    compileAndInternUnivCanon_list_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hlevelsList hstate hrefList
  refine ⟨compiled.toArray, state', ?_, ?_, hstate', harena, hcache⟩
  · rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind,
      run_bind compileEnv blockEnv state _ _, hrun]
    rfl
  · have hmapped := congrArg List.toArray hmap
    simpa using hmapped

/-- Arbitrary-universe local-mutual constant step. -/
theorem compileExprNoSurgeryStep_const_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash : Address} {indices : Array UInt64}
    {recIdx : Nat}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile
            (.const name levels hash)) =
        .ok ((.recur recIdx.toUInt64 indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨compiled, univState, hunivsRun, hindices, hunivState,
      hunivArena, hunivExprCache⟩ :=
    compileAndInternUnivCanon_array_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hlevels hstate hrefLevels
  let nameState := univState.compileName name
  have hnameState :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
    hunivState.compileName name
  let root := nameState.arena.nodes.size.toUInt64
  let allocated := allocState nameState (.ref name.getHash)
  have hallocated :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot allocated :=
    hnameState.alloc (.ref name.getHash)
  let patchIndices := compiled.map fun (canonical, original?) =>
    original?.getD canonical
  cases hpatch : compiled.any (·.2.isSome) with
  | false =>
    refine ⟨root, allocated, ?_, hallocated⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
      run_getBlockEnv]
    simp only
    rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
    simp only
    rw [hmut]
    rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
    simp [hpatch, hindices]
    rfl
  | true =>
    let finalState := patchState allocated root patchIndices
    refine ⟨root, finalState, ?_, hallocated.patch root patchIndices⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
      run_getBlockEnv]
    simp only
    rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
    simp only
    rw [hmut]
    rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
    simp only
    rw [hpatch]
    simp
    rw [map_eq_pure_bind]
    rw [run_bind compileEnv blockEnv allocated _ _, run_pushUnivPatch]
    simp [hindices]
    rfl

/-- Arbitrary-universe external constant step. -/
theorem compileExprNoSurgeryStep_const_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash addr : Address}
    {indices : Array UInt64} {refIdx : UInt64}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile
            (.const name levels hash)) =
        .ok ((.ref refIdx indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨compiled, univState, hunivsRun, hindices, hunivState,
      hunivArena, hunivExprCache⟩ :=
    compileAndInternUnivCanon_array_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hlevels hstate hrefLevels
  let nameState := univState.compileName name
  have hnameState :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
    hunivState.compileName name
  have hresolveName :
      resolveConstAddr? compileEnv nameState name = some addr := by
    rw [resolveConstAddr?_of_exprTableView_eq compileEnv hnameState.tables]
    exact hresolve
  have hmaps := refsIndex_eq_of_exprTableView_eq hnameState.tables
  have hindexName : nameState.refsIndex.get? addr = some refIdx := by
    rw [hmaps]
    exact hpreseed
  have hlookupRun := run_lookupConstAddr_resolved compileEnv blockEnv nameState
    name addr hresolveName
  have hinternRun := run_internRef_hit compileEnv blockEnv nameState addr
    refIdx hindexName
  let root := nameState.arena.nodes.size.toUInt64
  let allocated := allocState nameState (.ref name.getHash)
  have hallocated :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot allocated :=
    hnameState.alloc (.ref name.getHash)
  let patchIndices := compiled.map fun (canonical, original?) =>
    original?.getD canonical
  cases hpatch : compiled.any (·.2.isSome) with
  | false =>
    refine ⟨root, allocated, ?_, hallocated⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
      run_getBlockEnv]
    simp only
    rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
    simp only
    rw [hmut]
    rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
    simp [hpatch, hindices]
    rfl
  | true =>
    let finalState := patchState allocated root patchIndices
    refine ⟨root, finalState, ?_, hallocated.patch root patchIndices⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
      run_getBlockEnv]
    simp only
    rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
    simp only
    rw [hmut]
    rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
    simp only
    rw [hpatch]
    simp
    rw [map_eq_pure_bind]
    rw [run_bind compileEnv blockEnv allocated _ _, run_pushUnivPatch]
    simp [hindices]
    rfl

theorem compileExprNoSurgeryFuel_const_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash : Address} {indices : Array UInt64}
    {recIdx : Nat}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.const name levels hash)) =
        .ok ((.recur recIdx.toUInt64 indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmut' : blockEnv.mutCtx[name]? = some recIdx := by
    change blockEnv.mutCtx.get? name = some recIdx
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
        some recIdx.toUInt64 := by
    simp [frozenRefCompileCtx, hmut']
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name levels hash) =
        some (.recur recIdx.toUInt64 indices) := by
    simp [compileExprRef, hrefLevels, hctxMut]
  exact compileExprNoSurgeryFuel_leaf_refines compileEnv blockEnv snapshot
    hexprFaithful OrdinaryExpr.const hstate href fuel
    (compileExprNoSurgeryStep_const_recur_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful (Ix.CompileM.compileExprNoSurgeryFuel fuel)
      hlevels hstate hrefLevels hmut)

theorem compileExprNoSurgeryFuel_const_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash addr : Address}
    {indices : Array UInt64} {refIdx : UInt64}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.const name levels hash)) =
        .ok ((.ref refIdx indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmut' : blockEnv.mutCtx[name]? = none := by
    change blockEnv.mutCtx.get? name = none
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name = none := by
    simp [frozenRefCompileCtx, hmut']
  have hctxRef :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex name =
        some refIdx := by
    simp only [frozenRefCompileCtx]
    rw [show resolveConstAddr? compileEnv snapshot name = some addr from hresolve]
    change snapshot.refsIndex.get? addr = some refIdx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name levels hash) = some (.ref refIdx indices) := by
    simp [compileExprRef, hrefLevels, hctxMut, hctxRef]
  exact compileExprNoSurgeryFuel_leaf_refines compileEnv blockEnv snapshot
    hexprFaithful OrdinaryExpr.const hstate href fuel
    (compileExprNoSurgeryStep_const_ref_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful (Ix.CompileM.compileExprNoSurgeryFuel fuel)
      hlevels hstate hrefLevels hmut hresolve hpreseed)

theorem compileExpr_run_const_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash : Address} {indices : Array UInt64}
    {recIdx : Nat}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name levels hash)) =
        .ok ((.recur recIdx.toUInt64 indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgeryFuel_const_recur_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hexprFaithful hlevels hstate hrefLevels hmut 0
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  simpa [Ix.CompileM.compileExprNoSurgery,
    Ix.CompileM.exprCompileDepth] using hrun

theorem compileExpr_run_const_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name}
    {levels : Array Ix.Level} {hash addr : Address}
    {indices : Array UInt64} {refIdx : UInt64}
    (hlevels : ∀ level ∈ levels, levelSupport level)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefLevels : levels.mapM
      (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex =
        some indices)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name levels hash)) =
        .ok ((.ref refIdx indices, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgeryFuel_const_ref_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hexprFaithful hlevels hstate hrefLevels hmut
      hresolve hpreseed 0
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  simpa [Ix.CompileM.compileExprNoSurgery,
    Ix.CompileM.exprCompileDepth] using hrun

/-- Exact empty-universe local-mutual constant step.  It records the source
name, allocates reference metadata, and emits the block-local recursion index
without consulting or changing the external reference table. -/
theorem compileExprNoSurgeryStep_constEmpty_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash : Address}
    {recIdx : Nat}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile
            (.const name #[] hash)) =
        .ok ((.recur recIdx.toUInt64 #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  let nameState := state.compileName name
  have hnameState :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
    hstate.compileName name
  let root := nameState.arena.nodes.size.toUInt64
  let finalState := allocState nameState (.ref name.getHash)
  refine ⟨root, finalState, ?_, hnameState.alloc (.ref name.getHash)⟩
  rw [Ix.CompileM.compileExprNoSurgeryStep,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
    run_getBlockEnv]
  simp only [Array.mapM_empty]
  rw [run_bind compileEnv blockEnv state _ _, run_pure]
  simp only
  rw [run_bind compileEnv blockEnv state _ _, run_compileName]
  simp only
  rw [hmut]
  rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
  simp
  rfl

/-- Exact empty-universe external constant step against the frozen resolution
and reference tables.  The required `internRef` is necessarily a hit, so the
primary table remains frozen. -/
theorem compileExprNoSurgeryStep_constEmpty_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash : Address}
    {addr : Address} {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile
            (.const name #[] hash)) =
        .ok ((.ref refIdx #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  let nameState := state.compileName name
  have hnameState :
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
    hstate.compileName name
  have hresolveName :
      resolveConstAddr? compileEnv nameState name = some addr := by
    rw [resolveConstAddr?_of_exprTableView_eq compileEnv hnameState.tables]
    exact hresolve
  have hmaps := refsIndex_eq_of_exprTableView_eq hnameState.tables
  have hindexName : nameState.refsIndex.get? addr = some refIdx := by
    rw [hmaps]
    exact hpreseed
  have hlookupRun := run_lookupConstAddr_resolved compileEnv blockEnv nameState
    name addr hresolveName
  have hinternRun := run_internRef_hit compileEnv blockEnv nameState addr
    refIdx hindexName
  let root := nameState.arena.nodes.size.toUInt64
  let finalState := allocState nameState (.ref name.getHash)
  refine ⟨root, finalState, ?_, hnameState.alloc (.ref name.getHash)⟩
  rw [Ix.CompileM.compileExprNoSurgeryStep,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
    run_getBlockEnv]
  simp only [Array.mapM_empty]
  rw [run_bind compileEnv blockEnv state _ _, run_pure]
  simp only
  rw [run_bind compileEnv blockEnv state _ _, run_compileName]
  simp only
  rw [hmut]
  rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
  simp only
  rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
  simp only
  rw [run_bind compileEnv blockEnv nameState _ _, run_allocArenaNode]
  simp
  rfl

theorem compileExprNoSurgeryFuel_constEmpty_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash : Address}
    {recIdx : Nat}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.const name #[] hash)) =
        .ok ((.recur recIdx.toUInt64 #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmut' : blockEnv.mutCtx[name]? = some recIdx := by
    change blockEnv.mutCtx.get? name = some recIdx
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
        some recIdx.toUInt64 := by
    simp [frozenRefCompileCtx, hmut']
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name #[] hash) = some (.recur recIdx.toUInt64 #[]) := by
    simp [compileExprRef, hctxMut]
  exact compileExprNoSurgeryFuel_leaf_refines compileEnv blockEnv snapshot
    hexprFaithful OrdinaryExpr.const hstate href fuel
    (compileExprNoSurgeryStep_constEmpty_recur_refines compileEnv blockEnv
      snapshot (Ix.CompileM.compileExprNoSurgeryFuel fuel) hstate hmut)

theorem compileExprNoSurgeryFuel_constEmpty_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash addr : Address}
    {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.const name #[] hash)) =
        .ok ((.ref refIdx #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hmut' : blockEnv.mutCtx[name]? = none := by
    change blockEnv.mutCtx.get? name = none
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name = none := by
    simp [frozenRefCompileCtx, hmut']
  have hctxRef :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex name =
        some refIdx := by
    simp only [frozenRefCompileCtx]
    rw [show resolveConstAddr? compileEnv snapshot name = some addr from hresolve]
    change snapshot.refsIndex.get? addr = some refIdx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name #[] hash) = some (.ref refIdx #[]) := by
    simp [compileExprRef, hctxMut, hctxRef]
  exact compileExprNoSurgeryFuel_leaf_refines compileEnv blockEnv snapshot
    hexprFaithful OrdinaryExpr.const hstate href fuel
    (compileExprNoSurgeryStep_constEmpty_ref_refines compileEnv blockEnv
      snapshot (Ix.CompileM.compileExprNoSurgeryFuel fuel) hstate hmut hresolve
      hpreseed)

/-- Production compilation of an empty-universe local mutual reference. -/
theorem compileExpr_run_constEmpty_recur_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash : Address}
    {recIdx : Nat}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = some recIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name #[] hash)) =
        .ok ((.recur recIdx.toUInt64 #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgeryFuel_constEmpty_recur_refines compileEnv blockEnv
      snapshot hexprFaithful hstate hmut 0
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  simpa [Ix.CompileM.compileExprNoSurgery,
    Ix.CompileM.exprCompileDepth] using hrun

/-- Production compilation of an empty-universe external reference. -/
theorem compileExpr_run_constEmpty_ref_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash addr : Address}
    {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name #[] hash)) =
        .ok ((.ref refIdx #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgeryFuel_constEmpty_ref_refines compileEnv blockEnv snapshot
      hexprFaithful hstate hmut hresolve hpreseed 0
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  simpa [Ix.CompileM.compileExprNoSurgery,
    Ix.CompileM.exprCompileDepth] using hrun

theorem compileExpr_run_constEmpty_recur_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash : Address}
    {recIdx : Nat} {value : Lean4Lean.VExpr}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = some recIdx)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals
      (.const name #[] hash) value) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name #[] hash)) =
        .ok ((.recur recIdx.toUInt64 #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        (.recur recIdx.toUInt64 #[]) value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_constEmpty_recur_refines compileEnv blockEnv snapshot hfree
      hexprFaithful hstate hmut
  have hmut' : blockEnv.mutCtx[name]? = some recIdx := by
    change blockEnv.mutCtx.get? name = some recIdx
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
        some recIdx.toUInt64 := by
    simp [frozenRefCompileCtx, hmut']
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name #[] hash) = some (.recur recIdx.toUInt64 #[]) := by
    simp [compileExprRef, hctxMut]
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

theorem compileExpr_run_constEmpty_ref_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {name : Ix.Name} {hash addr : Address}
    {refIdx : UInt64} {value : Lean4Lean.VExpr}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hmut : blockEnv.mutCtx.get? name = none)
    (hresolve : resolveConstAddr? compileEnv snapshot name = some addr)
    (hpreseed : snapshot.refsIndex.get? addr = some refIdx)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals
      (.const name #[] hash) value) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.const name #[] hash)) =
        .ok ((.ref refIdx #[], root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        (.ref refIdx #[]) value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_constEmpty_ref_refines compileEnv blockEnv snapshot hfree
      hexprFaithful hstate hmut hresolve hpreseed
  have hmut' : blockEnv.mutCtx[name]? = none := by
    change blockEnv.mutCtx.get? name = none
    exact hmut
  have hctxMut :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name = none := by
    simp [frozenRefCompileCtx, hmut']
  have hctxRef :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex name =
        some refIdx := by
    simp only [frozenRefCompileCtx]
    rw [show resolveConstAddr? compileEnv snapshot name = some addr from hresolve]
    change snapshot.refsIndex.get? addr = some refIdx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.const name #[] hash) = some (.ref refIdx #[]) := by
    simp [compileExprRef, hctxMut, hctxRef]
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

/-- Exact production literal step.  Literal bytes are committed to the
sidecar blob map, while their address must already occupy the frozen primary
reference table; hence the subsequent interning transition is a hit. -/
theorem compileExprNoSurgeryStep_lit_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (compile : Ix.Expr → Ix.CompileM.CompileM (Ixon.Expr × UInt64))
    {state : Ix.CompileM.BlockState} {literal : Lean.Literal} {hash : Address}
    {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hpreseed : snapshot.refsIndex.get? (literalAddress literal) = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep compile
            (.lit literal hash)) =
        .ok ((literalExpr literal refIdx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  cases literal with
  | natVal value =>
    let bytes := ByteArray.mk (Nat.toBytesLE value)
    let addr := Address.blake3 bytes
    have hpreseed' : snapshot.refsIndex.get? addr = some refIdx := by
      simpa [addr, bytes, literalAddress] using hpreseed
    let blobbed := blobState state addr bytes
    have hblobbed :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot blobbed :=
      hstate.blob addr bytes
    have hmaps := refsIndex_eq_of_exprTableView_eq hblobbed.tables
    have hindex : blobbed.refsIndex.get? addr = some refIdx := by
      rw [hmaps]
      exact hpreseed'
    have hintern := run_internRef_hit compileEnv blockEnv blobbed addr refIdx
      hindex
    let root := blobbed.arena.nodes.size.toUInt64
    let finalState := allocState blobbed .leaf
    refine ⟨root, finalState, ?_, hblobbed.alloc .leaf⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _,
      run_insertBlockBlob compileEnv blockEnv state addr bytes]
    simp only
    rw [run_bind compileEnv blockEnv blobbed _ _, hintern]
    simp only
    rw [run_bind compileEnv blockEnv blobbed _ _, run_allocArenaNode]
    rfl
  | strVal value =>
    let bytes := value.toUTF8
    let addr := Address.blake3 bytes
    have hpreseed' : snapshot.refsIndex.get? addr = some refIdx := by
      simpa [addr, bytes, literalAddress] using hpreseed
    let blobbed := blobState state addr bytes
    have hblobbed :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot blobbed :=
      hstate.blob addr bytes
    have hmaps := refsIndex_eq_of_exprTableView_eq hblobbed.tables
    have hindex : blobbed.refsIndex.get? addr = some refIdx := by
      rw [hmaps]
      exact hpreseed'
    have hintern := run_internRef_hit compileEnv blockEnv blobbed addr refIdx
      hindex
    let root := blobbed.arena.nodes.size.toUInt64
    let finalState := allocState blobbed .leaf
    refine ⟨root, finalState, ?_, hblobbed.alloc .leaf⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _,
      run_insertBlockBlob compileEnv blockEnv state addr bytes]
    simp only
    rw [run_bind compileEnv blockEnv blobbed _ _, hintern]
    simp only
    rw [run_bind compileEnv blockEnv blobbed _ _, run_allocArenaNode]
    rfl

theorem compileExprNoSurgeryFuel_lit_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {literal : Lean.Literal} {hash : Address}
    {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hpreseed : snapshot.refsIndex.get? (literalAddress literal) = some refIdx)
    (fuel : Nat) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel (fuel + 1)
            (.lit literal hash)) =
        .ok ((literalExpr literal refIdx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  have hctxLiteral :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef literal =
        some refIdx := by
    simp only [frozenRefCompileCtx]
    change snapshot.refsIndex.get? (literalAddress literal) = some refIdx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.lit literal hash) = some (literalExpr literal refIdx) := by
    cases literal <;> simp [compileExprRef, literalExpr, hctxLiteral]
  exact compileExprNoSurgeryFuel_leaf_refines compileEnv blockEnv snapshot
    hexprFaithful OrdinaryExpr.lit hstate href fuel
    (compileExprNoSurgeryStep_lit_refines compileEnv blockEnv snapshot
      (Ix.CompileM.compileExprNoSurgeryFuel fuel) hstate hpreseed)

/-- Production compilation of a preseeded literal leaf. -/
theorem compileExpr_run_lit_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {literal : Lean.Literal} {hash : Address}
    {refIdx : UInt64}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hpreseed : snapshot.refsIndex.get? (literalAddress literal) = some refIdx) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.lit literal hash)) =
        .ok ((literalExpr literal refIdx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgeryFuel_lit_refines compileEnv blockEnv snapshot
      hexprFaithful hstate hpreseed 0
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  simpa [Ix.CompileM.compileExprNoSurgery,
    Ix.CompileM.exprCompileDepth] using hrun

theorem compileExpr_run_lit_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {literal : Lean.Literal} {hash : Address}
    {refIdx : UInt64} {value : Lean4Lean.VExpr}
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hpreseed : snapshot.refsIndex.get? (literalAddress literal) = some refIdx)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals
      (.lit literal hash) value) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr (.lit literal hash)) =
        .ok ((literalExpr literal refIdx, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        (literalExpr literal refIdx) value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_lit_refines compileEnv blockEnv snapshot hfree
      hexprFaithful hstate hpreseed
  have hctxLiteral :
      (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef literal =
        some refIdx := by
    simp only [frozenRefCompileCtx]
    change snapshot.refsIndex.get? (literalAddress literal) = some refIdx
    exact hpreseed
  have href :
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
          (.lit literal hash) = some (literalExpr literal refIdx) := by
    cases literal <;> simp [compileExprRef, literalExpr, hctxLiteral]
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

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

/-- Flattened App-spine refinement for the complete frozen ordinary domain. -/
private theorem compileAppNoSurgery_ordinary_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      SupportedOrdinaryExpr levelSupport source →
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state →
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot) source =
        some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state')
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAppNoSurgery
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  induction hsource generalizing state target with
  | bvar =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth SupportedOrdinaryExpr.bvar hstate href
  | sort hlevel =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.sort hlevel) hstate href
  | const hlevels =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.const hlevels) hstate href
  | lam hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.lam hty hbody) hstate href
  | all hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.all hty hbody) hstate href
  | letE hty hval hbody ihty ihval ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.letE hty hval hbody) hstate href
  | lit =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth SupportedOrdinaryExpr.lit hstate href
  | proj hval ihval =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.proj hval) hstate href
  | mdata hdata hinner ihinner =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.mdata hdata hinner) hstate href
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
    refine ⟨root, finalState, ?_, hargState.alloc (.app fnRoot argRoot)⟩
    rw [Ix.CompileM.compileAppNoSurgery.eq_1,
      run_bind compileEnv blockEnv state _ _, hfnRun]
    simp only
    rw [run_bind compileEnv blockEnv fnState _ _, hargRun]
    simp only
    rw [run_bind compileEnv blockEnv argState _ _, run_allocArenaNode]
    rfl

/-- Flattened App-spine refinement with the returned presentation-arena
tree, append-only growth, and warm-cache arena soundness. -/
private theorem compileAppNoSurgery_ordinary_arena_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      SupportedOrdinaryExpr levelSupport source →
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state →
      ArenaCacheWF state →
      state.arena.nodes.size + exprArenaCost source < UInt64.size →
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot) source =
        some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
        ArenaCacheWF state' ∧
        ArenaCompileRel source root state.arena state'.arena)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAppNoSurgery
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena := by
  induction hsource generalizing state target with
  | bvar =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth SupportedOrdinaryExpr.bvar hstate harena hroom href
  | sort hlevel =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.sort hlevel) hstate harena hroom href
  | const hlevels =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.const hlevels) hstate harena hroom href
  | lam hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.lam hty hbody) hstate harena hroom href
  | all hty hbody ihty ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.all hty hbody) hstate harena hroom href
  | letE hty hval hbody ihty ihval ihbody =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.letE hty hval hbody) hstate harena
        hroom href
  | lit =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth SupportedOrdinaryExpr.lit hstate harena hroom href
  | proj hval ihval =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.proj hval) hstate harena hroom href
  | mdata hdata hinner ihinner =>
    simpa [Ix.CompileM.compileAppNoSurgery] using
      hrecur hdepth (SupportedOrdinaryExpr.mdata hdata hinner) hstate harena
        hroom href
  | @app fn arg hash hfn harg ihfn iharg =>
    simp [compileExprRef] at href
    rcases href with ⟨fnTarget, hfnRef, argTarget, hargRef, rfl⟩
    have hfnDepth : Ix.CompileM.exprCompileDepth fn ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hargDepth : Ix.CompileM.exprCompileDepth arg ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hfnRoom :
        state.arena.nodes.size + exprArenaCost fn < UInt64.size := by
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨fnRoot, fnState, hfnRun, hfnState, hfnCache, hfnArena⟩ :=
      ihfn hfnDepth hstate harena hfnRoom hfnRef
    have hargRoom :
        fnState.arena.nodes.size + exprArenaCost arg < UInt64.size := by
      have hfnGrowth := hfnArena.growth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨argRoot, argState, hargRun, hargState, hargCache,
        hargArena⟩ :=
      hrecur hargDepth harg hfnState hfnCache hargRoom hargRef
    have hallocRoom : argState.arena.nodes.size < UInt64.size := by
      have hfnGrowth := hfnArena.growth
      have hargGrowth := hargArena.growth
      simp only [exprArenaCost] at hroom
      omega
    let root := argState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .app fnRoot argRoot
    let finalState := allocState argState node
    have hallocExtends : ArenaExtends argState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends argState node
    have hfnFinal : ArenaRel fn fnRoot finalState.arena :=
      hfnArena.rootRel.mono
        (ArenaExtends.trans hargArena.arenaExtends hallocExtends)
    have hargFinal : ArenaRel arg argRoot finalState.arena :=
      hargArena.rootRel.mono hallocExtends
    have hrootNode :
        finalState.arena.nodes[root.toNat]? = some (.app fnRoot argRoot) := by
      simpa [finalState, node, root] using
        allocState_root argState node hallocRoom
    have hrootRel :
        ArenaRel (.app fn arg hash) root finalState.arena :=
      .app hfnFinal hargFinal hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hargCache.of_frame (by rfl) hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤
          state.arena.nodes.size + exprArenaCost (.app fn arg hash) := by
      have hfnGrowth := hfnArena.growth
      have hargGrowth := hargArena.growth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hargState.alloc node, hfinalCache,
      ⟨hrootRel,
        ArenaExtends.trans hfnArena.arenaExtends
          (ArenaExtends.trans hargArena.arenaExtends hallocExtends),
        hfinalGrowth⟩⟩
    rw [Ix.CompileM.compileAppNoSurgery.eq_1,
      run_bind compileEnv blockEnv state _ _, hfnRun]
    simp only
    rw [run_bind compileEnv blockEnv fnState _ _, hargRun]
    simp only
    rw [run_bind compileEnv blockEnv argState _ _, run_allocArenaNode]
    rfl

/-- One cache-miss constructor step for the complete frozen ordinary domain. -/
private theorem compileExprNoSurgeryStep_ordinary_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      SupportedOrdinaryExpr levelSupport source →
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state →
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot) source =
        some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state')
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel + 1)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  cases hsource with
  | bvar =>
    simp [compileExprRef] at href
    subst target
    let root := state.arena.nodes.size.toUInt64
    let finalState := allocState state .leaf
    refine ⟨root, finalState, ?_, hstate.alloc .leaf⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_allocArenaNode]
    rfl
  | @sort level hash hlevel =>
    simp [compileExprRef] at href
    rcases href with ⟨idx, hctxIndex, rfl⟩
    exact compileExprNoSurgeryStep_sort_ctx_refines compileEnv blockEnv
      snapshot hclosed hlevelFaithful
      (Ix.CompileM.compileExprNoSurgeryFuel fuel) hlevel hstate hctxIndex
  | @const name levels hash hlevels =>
    cases hrefLevels : levels.mapM
        (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex with
    | none => simp [compileExprRef, hrefLevels] at href
    | some indices =>
      cases hmut : blockEnv.mutCtx.get? name with
      | some recIdx =>
        have hmut' : blockEnv.mutCtx[name]? = some recIdx := by
          change blockEnv.mutCtx.get? name = some recIdx
          exact hmut
        have hctxMut :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
              some recIdx.toUInt64 := by
          simp [frozenRefCompileCtx, hmut']
        simp [compileExprRef, hrefLevels, hctxMut] at href
        subst target
        exact compileExprNoSurgeryStep_const_recur_refines compileEnv blockEnv
          snapshot hclosed hlevelFaithful
          (Ix.CompileM.compileExprNoSurgeryFuel fuel) hlevels hstate
          hrefLevels hmut
      | none =>
        have hmut' : blockEnv.mutCtx[name]? = none := by
          change blockEnv.mutCtx.get? name = none
          exact hmut
        have hctxMut :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
              none := by
          simp [frozenRefCompileCtx, hmut']
        cases hresolve : resolveConstAddr? compileEnv snapshot name with
        | none =>
          have hctxRef :
              (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex name =
                none := by
            simp only [frozenRefCompileCtx]
            rw [hresolve]
            rfl
          simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
        | some addr =>
          cases hpreseed : snapshot.refsIndex.get? addr with
          | none =>
            have hctxRef :
                (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                    name = none := by
              simp only [frozenRefCompileCtx]
              rw [hresolve]
              change snapshot.refsIndex.get? addr = none
              exact hpreseed
            simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
          | some refIdx =>
            have hctxRef :
                (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                    name = some refIdx := by
              simp only [frozenRefCompileCtx]
              rw [hresolve]
              change snapshot.refsIndex.get? addr = some refIdx
              exact hpreseed
            simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
            subst target
            exact compileExprNoSurgeryStep_const_ref_refines compileEnv
              blockEnv snapshot hclosed hlevelFaithful
              (Ix.CompileM.compileExprNoSurgeryFuel fuel) hlevels hstate
              hrefLevels hmut hresolve hpreseed
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
      compileAppNoSurgery_ordinary_refines compileEnv blockEnv snapshot fuel
        hrecur hfnDepth hfn hstate hfnRef
    obtain ⟨argRoot, argState, hargRun, hargState⟩ :=
      hrecur hargDepth harg hfnState hargRef
    let root := argState.arena.nodes.size.toUInt64
    let finalState := allocState argState (.app fnRoot argRoot)
    refine ⟨root, finalState, ?_, hargState.alloc (.app fnRoot argRoot)⟩
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
    have hnameState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
      hstate.compileName name
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody htyState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let finalState := allocState bodyState (.binder name.getHash bi tyRoot bodyRoot)
    refine ⟨root, finalState, ?_,
      hbodyState.alloc (.binder name.getHash bi tyRoot bodyRoot)⟩
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
    have hnameState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
      hstate.compileName name
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody htyState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let finalState := allocState bodyState (.binder name.getHash bi tyRoot bodyRoot)
    refine ⟨root, finalState, ?_,
      hbodyState.alloc (.binder name.getHash bi tyRoot bodyRoot)⟩
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
    have hnameState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot nameState :=
      hstate.compileName name
    obtain ⟨tyRoot, tyState, htyRun, htyState⟩ :=
      hrecur htyDepth hty hnameState htyRef
    obtain ⟨valRoot, valState, hvalRun, hvalState⟩ :=
      hrecur hvalDepth hval htyState hvalRef
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState⟩ :=
      hrecur hbodyDepth hbody hvalState hbodyRef
    let root := bodyState.arena.nodes.size.toUInt64
    let finalState := allocState bodyState
      (.letBinder name.getHash tyRoot valRoot bodyRoot)
    refine ⟨root, finalState, ?_,
      hbodyState.alloc (.letBinder name.getHash tyRoot valRoot bodyRoot)⟩
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
  | @lit literal hash =>
    cases hpreseed : snapshot.refsIndex.get? (literalAddress literal) with
    | none =>
      have hctxLiteral :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef
              literal = none := by
        simp only [frozenRefCompileCtx]
        change snapshot.refsIndex.get? (literalAddress literal) = none
        exact hpreseed
      simp [compileExprRef, hctxLiteral] at href
    | some refIdx =>
      have hctxLiteral :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef
              literal = some refIdx := by
        simp only [frozenRefCompileCtx]
        change snapshot.refsIndex.get? (literalAddress literal) = some refIdx
        exact hpreseed
      have hexpected :
          compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
              (.lit literal hash) = some (literalExpr literal refIdx) := by
        cases literal <;> simp [compileExprRef, literalExpr, hctxLiteral]
      have htarget : target = literalExpr literal refIdx :=
        Option.some.inj (href.symm.trans hexpected)
      subst target
      exact compileExprNoSurgeryStep_lit_refines compileEnv blockEnv snapshot
        (Ix.CompileM.compileExprNoSurgeryFuel fuel) hstate hpreseed
  | @proj typeName field val hash hval =>
    cases hresolve : resolveConstAddr? compileEnv snapshot typeName with
    | none =>
      have hctxRef :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
              typeName = none := by
        simp only [frozenRefCompileCtx]
        rw [hresolve]
        rfl
      simp [compileExprRef, hctxRef] at href
    | some addr =>
      cases hpreseed : snapshot.refsIndex.get? addr with
      | none =>
        have hctxRef :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                typeName = none := by
          simp only [frozenRefCompileCtx]
          rw [hresolve]
          change snapshot.refsIndex.get? addr = none
          exact hpreseed
        simp [compileExprRef, hctxRef] at href
      | some refIdx =>
        have hctxRef :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                typeName = some refIdx := by
          simp only [frozenRefCompileCtx]
          rw [hresolve]
          change snapshot.refsIndex.get? addr = some refIdx
          exact hpreseed
        simp [compileExprRef, hctxRef] at href
        rcases href with ⟨valTarget, hvalRef, rfl⟩
        have hvalDepth : Ix.CompileM.exprCompileDepth val ≤ fuel := by
          simp only [Ix.CompileM.exprCompileDepth] at hdepth
          omega
        let nameState := state.compileName typeName
        have hnameState :
            FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
              nameState := hstate.compileName typeName
        have hresolveName :
            resolveConstAddr? compileEnv nameState typeName = some addr := by
          rw [resolveConstAddr?_of_exprTableView_eq compileEnv
            hnameState.tables]
          exact hresolve
        have hmaps := refsIndex_eq_of_exprTableView_eq hnameState.tables
        have hindexName : nameState.refsIndex.get? addr = some refIdx := by
          rw [hmaps]
          exact hpreseed
        have hlookupRun := run_lookupConstAddr_resolved compileEnv blockEnv
          nameState typeName addr hresolveName
        have hinternRun := run_internRef_hit compileEnv blockEnv nameState addr
          refIdx hindexName
        obtain ⟨valRoot, valState, hvalRun, hvalState⟩ :=
          hrecur hvalDepth hval hnameState hvalRef
        let root := valState.arena.nodes.size.toUInt64
        let finalState := allocState valState (.prj typeName.getHash valRoot)
        refine ⟨root, finalState, ?_,
          hvalState.alloc (.prj typeName.getHash valRoot)⟩
        rw [Ix.CompileM.compileExprNoSurgeryStep,
          run_bind compileEnv blockEnv state _ _, run_compileName]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hvalRun]
        simp only
        rw [run_bind compileEnv blockEnv valState _ _, run_allocArenaNode]
        rfl
  | @mdata data inner hash hdata hinner =>
    have hinnerRef :
        compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
            inner = some target := by
      simpa [compileExprRef] using href
    have hinnerDepth : Ix.CompileM.exprCompileDepth inner ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    obtain ⟨kvmap, hkvmapRef⟩ := hdata
    obtain ⟨metaState, hmetaRun, hmetaFrame⟩ :=
      compileKVMap_run_refines compileEnv blockEnv state hkvmapRef
    have hmetaState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot metaState :=
      hstate.of_metaFrame hmetaFrame
    obtain ⟨innerRoot, innerState, hinnerRun, hinnerState⟩ :=
      hrecur hinnerDepth hinner hmetaState hinnerRef
    let root := innerState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .mdata #[kvmap] innerRoot
    let finalState := allocState innerState node
    refine ⟨root, finalState, ?_,
      hinnerState.alloc node⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, hmetaRun]
    simp only
    rw [run_bind compileEnv blockEnv metaState _ _, hinnerRun]
    simp only
    rw [run_bind compileEnv blockEnv innerState _ _, run_allocArenaNode]
    rfl

/-- One cache-miss constructor step with semantic refinement and the complete
presentation-arena transition. -/
private theorem compileExprNoSurgeryStep_ordinary_arena_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (fuel : Nat)
    (hrecur : ∀ {state : Ix.CompileM.BlockState} {source : Ix.Expr}
        {target : Ixon.Expr},
      Ix.CompileM.exprCompileDepth source ≤ fuel →
      SupportedOrdinaryExpr levelSupport source →
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state →
      ArenaCacheWF state →
      state.arena.nodes.size + exprArenaCost source < UInt64.size →
      compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot) source =
        some target →
      ∃ root state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state
            (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
          .ok ((target, root), state') ∧
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
        ArenaCacheWF state' ∧
        ArenaCompileRel source root state.arena state'.arena)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel + 1)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryStep
            (Ix.CompileM.compileExprNoSurgeryFuel fuel) source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena := by
  cases hsource with
  | bvar =>
    simp [compileExprRef] at href
    subst target
    let root := state.arena.nodes.size.toUInt64
    let finalState := allocState state .leaf
    obtain ⟨hfinalCache, hextends, hgrowth, hnode⟩ :=
      arenaLeafFrame harena rfl rfl .leaf (by
        simpa [exprArenaCost] using hroom)
    refine ⟨root, finalState, ?_, hstate.alloc .leaf, hfinalCache,
      ⟨ArenaRel.bvar hnode, hextends, hgrowth⟩⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, run_allocArenaNode]
    rfl
  | @sort level hash hlevel =>
    simp [compileExprRef] at href
    rcases href with ⟨idx, hctxIndex, rfl⟩
    obtain ⟨original?, univState, hunivRun, hunivState, hunivArena,
        hunivCache⟩ :=
      hstate.compileAndInternUnivCanon_refines compileEnv blockEnv snapshot
        hclosed hlevelFaithful hlevel hctxIndex
    let root := univState.arena.nodes.size.toUInt64
    let allocated := allocState univState .leaf
    have hleafRoom : state.arena.nodes.size + 1 < UInt64.size := by
      simpa [exprArenaCost] using hroom
    obtain ⟨hallocatedCache, hextends, hgrowth, hnode⟩ :=
      arenaLeafFrame harena hunivCache hunivArena .leaf hleafRoom
    have hallocatedState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot allocated :=
      hunivState.alloc .leaf
    cases original? with
    | none =>
      refine ⟨root, allocated, ?_, hallocatedState, hallocatedCache,
        ⟨ArenaRel.sort hnode, hextends, ?_⟩⟩
      · rw [Ix.CompileM.compileExprNoSurgeryStep,
          run_bind compileEnv blockEnv state _ _, hunivRun]
        simp only
        rw [run_bind compileEnv blockEnv univState _ _, run_allocArenaNode]
        rfl
      · simpa [exprArenaCost] using hgrowth
    | some original =>
      let finalState := patchState allocated root #[original]
      have hpatchExtends : ArenaExtends allocated.arena finalState.arena := by
        change ArenaExtends allocated.arena allocated.arena
        exact ArenaExtends.refl allocated.arena
      have hfinalCache : ArenaCacheWF finalState :=
        hallocatedCache.of_frame rfl hpatchExtends
      have hfinalState :
          FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
            finalState := hallocatedState.patch root #[original]
      refine ⟨root, finalState, ?_, hfinalState, hfinalCache,
        ⟨(ArenaRel.sort hnode).mono hpatchExtends,
          ArenaExtends.trans hextends hpatchExtends, ?_⟩⟩
      · rw [Ix.CompileM.compileExprNoSurgeryStep,
          run_bind compileEnv blockEnv state _ _, hunivRun]
        simp only
        rw [run_bind compileEnv blockEnv univState _ _, run_allocArenaNode]
        simp only
        rw [run_bind compileEnv blockEnv allocated _ _, run_pushUnivPatch]
        rfl
      · change allocated.arena.nodes.size ≤
          state.arena.nodes.size + exprArenaCost (.sort level hash)
        simpa [exprArenaCost] using hgrowth
  | @const name levels hash hlevels =>
    cases hrefLevels : levels.mapM
        (frozenRefCompileCtx compileEnv blockEnv snapshot).univIndex with
    | none => simp [compileExprRef, hrefLevels] at href
    | some indices =>
      obtain ⟨compiled, univState, hunivsRun, hindices, hunivState,
          hunivArena, hunivCache⟩ :=
        compileAndInternUnivCanon_array_refines compileEnv blockEnv snapshot
          hclosed hlevelFaithful hlevels hstate hrefLevels
      let nameState := univState.compileName name
      have hnameState :
          FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
            nameState := hunivState.compileName name
      have hnameArena : nameState.arena = state.arena :=
        (BlockState.compileName_arena univState name).trans hunivArena
      have hnameCache : nameState.exprCache = state.exprCache :=
        (BlockState.compileName_exprCache univState name).trans hunivCache
      let root := nameState.arena.nodes.size.toUInt64
      let allocated := allocState nameState (.ref name.getHash)
      have hleafRoom : state.arena.nodes.size + 1 < UInt64.size := by
        simpa [exprArenaCost] using hroom
      obtain ⟨hallocatedCache, hextends, hgrowth, hnode⟩ :=
        arenaLeafFrame harena hnameCache hnameArena (.ref name.getHash)
          hleafRoom
      have hallocatedState :
          FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
            allocated := hnameState.alloc (.ref name.getHash)
      let patchIndices := compiled.map fun (canonical, original?) =>
        original?.getD canonical
      cases hmut : blockEnv.mutCtx.get? name with
      | some recIdx =>
        have hmut' : blockEnv.mutCtx[name]? = some recIdx := by
          change blockEnv.mutCtx.get? name = some recIdx
          exact hmut
        have hctxMut :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
              some recIdx.toUInt64 := by
          simp [frozenRefCompileCtx, hmut']
        simp [compileExprRef, hrefLevels, hctxMut] at href
        subst target
        cases hpatch : compiled.any (·.2.isSome) with
        | false =>
          refine ⟨root, allocated, ?_, hallocatedState, hallocatedCache,
            ⟨ArenaRel.const hnode, hextends, ?_⟩⟩
          · rw [Ix.CompileM.compileExprNoSurgeryStep,
              run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
              run_getBlockEnv]
            simp only
            rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
            simp only
            rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
            simp only
            rw [hmut]
            rw [run_bind compileEnv blockEnv nameState _ _,
              run_allocArenaNode]
            simp [hpatch, hindices]
            rfl
          · simpa [exprArenaCost] using hgrowth
        | true =>
          let finalState := patchState allocated root patchIndices
          have hpatchExtends :
              ArenaExtends allocated.arena finalState.arena := by
            change ArenaExtends allocated.arena allocated.arena
            exact ArenaExtends.refl allocated.arena
          have hfinalCache : ArenaCacheWF finalState :=
            hallocatedCache.of_frame rfl hpatchExtends
          have hfinalState :
              FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
                finalState := hallocatedState.patch root patchIndices
          refine ⟨root, finalState, ?_, hfinalState, hfinalCache,
            ⟨(ArenaRel.const hnode).mono hpatchExtends,
              ArenaExtends.trans hextends hpatchExtends, ?_⟩⟩
          · rw [Ix.CompileM.compileExprNoSurgeryStep,
              run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
              run_getBlockEnv]
            simp only
            rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
            simp only
            rw [run_bind compileEnv blockEnv univState _ _, run_compileName]
            simp only
            rw [hmut]
            rw [run_bind compileEnv blockEnv nameState _ _,
              run_allocArenaNode]
            simp only
            rw [hpatch]
            simp
            rw [map_eq_pure_bind]
            rw [run_bind compileEnv blockEnv allocated _ _,
              run_pushUnivPatch]
            simp [hindices]
            rfl
          · change allocated.arena.nodes.size ≤
              state.arena.nodes.size +
                exprArenaCost (.const name levels hash)
            simpa [exprArenaCost] using hgrowth
      | none =>
        have hmut' : blockEnv.mutCtx[name]? = none := by
          change blockEnv.mutCtx.get? name = none
          exact hmut
        have hctxMut :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).mutIndex name =
              none := by
          simp [frozenRefCompileCtx, hmut']
        cases hresolve : resolveConstAddr? compileEnv snapshot name with
        | none =>
          have hctxRef :
              (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex name =
                none := by
            simp only [frozenRefCompileCtx]
            rw [hresolve]
            rfl
          simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
        | some addr =>
          cases hpreseed : snapshot.refsIndex.get? addr with
          | none =>
            have hctxRef :
                (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                    name = none := by
              simp only [frozenRefCompileCtx]
              rw [hresolve]
              change snapshot.refsIndex.get? addr = none
              exact hpreseed
            simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
          | some refIdx =>
            have hctxRef :
                (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                    name = some refIdx := by
              simp only [frozenRefCompileCtx]
              rw [hresolve]
              change snapshot.refsIndex.get? addr = some refIdx
              exact hpreseed
            simp [compileExprRef, hrefLevels, hctxMut, hctxRef] at href
            subst target
            have hresolveName :
                resolveConstAddr? compileEnv nameState name = some addr := by
              rw [resolveConstAddr?_of_exprTableView_eq compileEnv
                hnameState.tables]
              exact hresolve
            have hmaps := refsIndex_eq_of_exprTableView_eq hnameState.tables
            have hindexName : nameState.refsIndex.get? addr = some refIdx := by
              rw [hmaps]
              exact hpreseed
            have hlookupRun := run_lookupConstAddr_resolved compileEnv blockEnv
              nameState name addr hresolveName
            have hinternRun := run_internRef_hit compileEnv blockEnv nameState
              addr refIdx hindexName
            cases hpatch : compiled.any (·.2.isSome) with
            | false =>
              refine ⟨root, allocated, ?_, hallocatedState, hallocatedCache,
                ⟨ArenaRel.const hnode, hextends, ?_⟩⟩
              · rw [Ix.CompileM.compileExprNoSurgeryStep,
                  run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
                  run_getBlockEnv]
                simp only
                rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
                simp only
                rw [run_bind compileEnv blockEnv univState _ _,
                  run_compileName]
                simp only
                rw [hmut]
                rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
                simp only
                rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
                simp only
                rw [run_bind compileEnv blockEnv nameState _ _,
                  run_allocArenaNode]
                simp [hpatch, hindices]
                rfl
              · simpa [exprArenaCost] using hgrowth
            | true =>
              let finalState := patchState allocated root patchIndices
              have hpatchExtends :
                  ArenaExtends allocated.arena finalState.arena := by
                change ArenaExtends allocated.arena allocated.arena
                exact ArenaExtends.refl allocated.arena
              have hfinalCache : ArenaCacheWF finalState :=
                hallocatedCache.of_frame rfl hpatchExtends
              have hfinalState :
                  FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
                    finalState := hallocatedState.patch root patchIndices
              refine ⟨root, finalState, ?_, hfinalState, hfinalCache,
                ⟨(ArenaRel.const hnode).mono hpatchExtends,
                  ArenaExtends.trans hextends hpatchExtends, ?_⟩⟩
              · rw [Ix.CompileM.compileExprNoSurgeryStep,
                  run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
                  run_getBlockEnv]
                simp only
                rw [run_bind compileEnv blockEnv state _ _, hunivsRun]
                simp only
                rw [run_bind compileEnv blockEnv univState _ _,
                  run_compileName]
                simp only
                rw [hmut]
                rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
                simp only
                rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
                simp only
                rw [run_bind compileEnv blockEnv nameState _ _,
                  run_allocArenaNode]
                simp only
                rw [hpatch]
                simp
                rw [map_eq_pure_bind]
                rw [run_bind compileEnv blockEnv allocated _ _,
                  run_pushUnivPatch]
                simp [hindices]
                rfl
              · change allocated.arena.nodes.size ≤
                  state.arena.nodes.size +
                    exprArenaCost (.const name levels hash)
                simpa [exprArenaCost] using hgrowth
  | @app fn arg hash hfn harg =>
    simp [compileExprRef] at href
    rcases href with ⟨fnTarget, hfnRef, argTarget, hargRef, rfl⟩
    have hfnDepth : Ix.CompileM.exprCompileDepth fn ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hargDepth : Ix.CompileM.exprCompileDepth arg ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    have hfnRoom :
        state.arena.nodes.size + exprArenaCost fn < UInt64.size := by
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨fnRoot, fnState, hfnRun, hfnState, hfnCache, hfnArena⟩ :=
      compileAppNoSurgery_ordinary_arena_refines compileEnv blockEnv snapshot
        fuel hrecur hfnDepth hfn hstate harena hfnRoom hfnRef
    have hargRoom :
        fnState.arena.nodes.size + exprArenaCost arg < UInt64.size := by
      have hfnGrowth := hfnArena.growth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨argRoot, argState, hargRun, hargState, hargCache,
        hargArena⟩ :=
      hrecur hargDepth harg hfnState hfnCache hargRoom hargRef
    have hallocRoom : argState.arena.nodes.size < UInt64.size := by
      have hfnGrowth := hfnArena.growth
      have hargGrowth := hargArena.growth
      simp only [exprArenaCost] at hroom
      omega
    let root := argState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .app fnRoot argRoot
    let finalState := allocState argState node
    have hallocExtends : ArenaExtends argState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends argState node
    have hrootNode :
        finalState.arena.nodes[root.toNat]? = some (.app fnRoot argRoot) := by
      simpa [finalState, node, root] using
        allocState_root argState node hallocRoom
    have hrootRel : ArenaRel (.app fn arg hash) root finalState.arena :=
      .app
        (hfnArena.rootRel.mono
          (ArenaExtends.trans hargArena.arenaExtends hallocExtends))
        (hargArena.rootRel.mono hallocExtends) hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hargCache.of_frame rfl hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤
          state.arena.nodes.size + exprArenaCost (.app fn arg hash) := by
      have hfnGrowth := hfnArena.growth
      have hargGrowth := hargArena.growth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hargState.alloc node, hfinalCache,
      ⟨hrootRel,
        ArenaExtends.trans hfnArena.arenaExtends
          (ArenaExtends.trans hargArena.arenaExtends hallocExtends),
        hfinalGrowth⟩⟩
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
    have hnameState := hstate.compileName name
    have hnameArenaEq : nameState.arena = state.arena :=
      BlockState.compileName_arena state name
    have hnameCacheEq : nameState.exprCache = state.exprCache :=
      BlockState.compileName_exprCache state name
    have hnameCache : ArenaCacheWF nameState :=
      harena.of_frame hnameCacheEq (by
        rw [hnameArenaEq]
        exact ArenaExtends.refl state.arena)
    have htyRoom :
        nameState.arena.nodes.size + exprArenaCost ty < UInt64.size := by
      rw [hnameArenaEq]
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨tyRoot, tyState, htyRun, htyState, htyCache, htyArena⟩ :=
      hrecur htyDepth hty hnameState hnameCache htyRoom htyRef
    have hbodyRoom :
        tyState.arena.nodes.size + exprArenaCost body < UInt64.size := by
      have htyGrowth := htyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState, hbodyCache,
        hbodyArena⟩ :=
      hrecur hbodyDepth hbody htyState htyCache hbodyRoom hbodyRef
    have hallocRoom : bodyState.arena.nodes.size < UInt64.size := by
      have htyGrowth := htyArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    let root := bodyState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .binder name.getHash bi tyRoot bodyRoot
    let finalState := allocState bodyState node
    have hallocExtends : ArenaExtends bodyState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends bodyState node
    have hrootNode : finalState.arena.nodes[root.toNat]? = some node := by
      simpa [finalState, root] using allocState_root bodyState node hallocRoom
    have hrootRel : ArenaRel (.lam name ty body bi hash) root finalState.arena :=
      .lam
        (htyArena.rootRel.mono
          (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends))
        (hbodyArena.rootRel.mono hallocExtends) hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hbodyCache.of_frame rfl hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤
          state.arena.nodes.size + exprArenaCost (.lam name ty body bi hash) := by
      have htyGrowth := htyArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hbodyState.alloc node, hfinalCache,
      ⟨hrootRel,
        ArenaExtends.trans (by
          rw [← hnameArenaEq]
          exact htyArena.arenaExtends)
          (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends),
        hfinalGrowth⟩⟩
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
    have hnameState := hstate.compileName name
    have hnameArenaEq : nameState.arena = state.arena :=
      BlockState.compileName_arena state name
    have hnameCacheEq : nameState.exprCache = state.exprCache :=
      BlockState.compileName_exprCache state name
    have hnameCache : ArenaCacheWF nameState :=
      harena.of_frame hnameCacheEq (by
        rw [hnameArenaEq]
        exact ArenaExtends.refl state.arena)
    have htyRoom :
        nameState.arena.nodes.size + exprArenaCost ty < UInt64.size := by
      rw [hnameArenaEq]
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨tyRoot, tyState, htyRun, htyState, htyCache, htyArena⟩ :=
      hrecur htyDepth hty hnameState hnameCache htyRoom htyRef
    have hbodyRoom :
        tyState.arena.nodes.size + exprArenaCost body < UInt64.size := by
      have htyGrowth := htyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState, hbodyCache,
        hbodyArena⟩ :=
      hrecur hbodyDepth hbody htyState htyCache hbodyRoom hbodyRef
    have hallocRoom : bodyState.arena.nodes.size < UInt64.size := by
      have htyGrowth := htyArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    let root := bodyState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .binder name.getHash bi tyRoot bodyRoot
    let finalState := allocState bodyState node
    have hallocExtends : ArenaExtends bodyState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends bodyState node
    have hrootNode : finalState.arena.nodes[root.toNat]? = some node := by
      simpa [finalState, root] using allocState_root bodyState node hallocRoom
    have hrootRel :
        ArenaRel (.forallE name ty body bi hash) root finalState.arena :=
      .all
        (htyArena.rootRel.mono
          (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends))
        (hbodyArena.rootRel.mono hallocExtends) hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hbodyCache.of_frame rfl hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤ state.arena.nodes.size +
          exprArenaCost (.forallE name ty body bi hash) := by
      have htyGrowth := htyArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hbodyState.alloc node, hfinalCache,
      ⟨hrootRel,
        ArenaExtends.trans (by
          rw [← hnameArenaEq]
          exact htyArena.arenaExtends)
          (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends),
        hfinalGrowth⟩⟩
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
    have hnameState := hstate.compileName name
    have hnameArenaEq : nameState.arena = state.arena :=
      BlockState.compileName_arena state name
    have hnameCacheEq : nameState.exprCache = state.exprCache :=
      BlockState.compileName_exprCache state name
    have hnameCache : ArenaCacheWF nameState :=
      harena.of_frame hnameCacheEq (by
        rw [hnameArenaEq]
        exact ArenaExtends.refl state.arena)
    have htyRoom :
        nameState.arena.nodes.size + exprArenaCost ty < UInt64.size := by
      rw [hnameArenaEq]
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨tyRoot, tyState, htyRun, htyState, htyCache, htyArena⟩ :=
      hrecur htyDepth hty hnameState hnameCache htyRoom htyRef
    have hvalRoom :
        tyState.arena.nodes.size + exprArenaCost val < UInt64.size := by
      have htyGrowth := htyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨valRoot, valState, hvalRun, hvalState, hvalCache, hvalArena⟩ :=
      hrecur hvalDepth hval htyState htyCache hvalRoom hvalRef
    have hbodyRoom :
        valState.arena.nodes.size + exprArenaCost body < UInt64.size := by
      have htyGrowth := htyArena.growth
      have hvalGrowth := hvalArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨bodyRoot, bodyState, hbodyRun, hbodyState, hbodyCache,
        hbodyArena⟩ :=
      hrecur hbodyDepth hbody hvalState hvalCache hbodyRoom hbodyRef
    have hallocRoom : bodyState.arena.nodes.size < UInt64.size := by
      have htyGrowth := htyArena.growth
      have hvalGrowth := hvalArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost] at hroom
      omega
    let root := bodyState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData :=
      .letBinder name.getHash tyRoot valRoot bodyRoot
    let finalState := allocState bodyState node
    have hallocExtends : ArenaExtends bodyState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends bodyState node
    have hrootNode : finalState.arena.nodes[root.toNat]? = some node := by
      simpa [finalState, root] using allocState_root bodyState node hallocRoom
    have hrootRel :
        ArenaRel (.letE name ty val body nonDep hash) root finalState.arena :=
      .letE
        (htyArena.rootRel.mono
          (ArenaExtends.trans hvalArena.arenaExtends
            (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends)))
        (hvalArena.rootRel.mono
          (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends))
        (hbodyArena.rootRel.mono hallocExtends) hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hbodyCache.of_frame rfl hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤ state.arena.nodes.size +
          exprArenaCost (.letE name ty val body nonDep hash) := by
      have htyGrowth := htyArena.growth
      have hvalGrowth := hvalArena.growth
      have hbodyGrowth := hbodyArena.growth
      rw [hnameArenaEq] at htyGrowth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hbodyState.alloc node, hfinalCache,
      ⟨hrootRel,
        ArenaExtends.trans (by
          rw [← hnameArenaEq]
          exact htyArena.arenaExtends)
          (ArenaExtends.trans hvalArena.arenaExtends
            (ArenaExtends.trans hbodyArena.arenaExtends hallocExtends)),
        hfinalGrowth⟩⟩
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
  | @lit literal hash =>
    cases hpreseed : snapshot.refsIndex.get? (literalAddress literal) with
    | none =>
      have hctxLiteral :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef
              literal = none := by
        simp only [frozenRefCompileCtx]
        change snapshot.refsIndex.get? (literalAddress literal) = none
        exact hpreseed
      simp [compileExprRef, hctxLiteral] at href
    | some refIdx =>
      have hctxLiteral :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).literalRef
              literal = some refIdx := by
        simp only [frozenRefCompileCtx]
        change snapshot.refsIndex.get? (literalAddress literal) = some refIdx
        exact hpreseed
      have hexpected :
          compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
              (.lit literal hash) = some (literalExpr literal refIdx) := by
        cases literal <;> simp [compileExprRef, literalExpr, hctxLiteral]
      have htarget : target = literalExpr literal refIdx :=
        Option.some.inj (href.symm.trans hexpected)
      subst target
      have hleafRoom : state.arena.nodes.size + 1 < UInt64.size := by
        simpa [exprArenaCost] using hroom
      cases literal with
      | natVal value =>
        let bytes := ByteArray.mk (Nat.toBytesLE value)
        let addr := Address.blake3 bytes
        have hpreseed' : snapshot.refsIndex.get? addr = some refIdx := by
          simpa [addr, bytes, literalAddress] using hpreseed
        let blobbed := blobState state addr bytes
        have hblobbed := hstate.blob addr bytes
        have hmaps := refsIndex_eq_of_exprTableView_eq hblobbed.tables
        have hindex : blobbed.refsIndex.get? addr = some refIdx := by
          rw [hmaps]
          exact hpreseed'
        have hintern := run_internRef_hit compileEnv blockEnv blobbed addr refIdx
          hindex
        let root := blobbed.arena.nodes.size.toUInt64
        let finalState := allocState blobbed .leaf
        obtain ⟨hfinalCache, hextends, hgrowth, hnode⟩ :=
          arenaLeafFrame (before := state) (middle := blobbed) harena rfl rfl
            .leaf hleafRoom
        have hfinalCache' : ArenaCacheWF finalState := by
          dsimp [finalState]
          exact hfinalCache
        have hextends' : ArenaExtends state.arena finalState.arena := by
          dsimp [finalState]
          exact hextends
        have hnode' : finalState.arena.nodes[root.toNat]? = some .leaf := by
          dsimp [finalState, root]
          exact hnode
        refine ⟨root, finalState, ?_, hblobbed.alloc .leaf, hfinalCache',
          ⟨ArenaRel.lit hnode', hextends', ?_⟩⟩
        · rw [Ix.CompileM.compileExprNoSurgeryStep,
            run_bind compileEnv blockEnv state _ _,
            run_insertBlockBlob compileEnv blockEnv state addr bytes]
          simp only
          rw [run_bind compileEnv blockEnv blobbed _ _, hintern]
          simp only
          rw [run_bind compileEnv blockEnv blobbed _ _, run_allocArenaNode]
          rfl
        · change (allocState blobbed .leaf).arena.nodes.size ≤
            state.arena.nodes.size + exprArenaCost (.lit (.natVal value) hash)
          simpa [exprArenaCost] using hgrowth
      | strVal value =>
        let bytes := value.toUTF8
        let addr := Address.blake3 bytes
        have hpreseed' : snapshot.refsIndex.get? addr = some refIdx := by
          simpa [addr, bytes, literalAddress] using hpreseed
        let blobbed := blobState state addr bytes
        have hblobbed := hstate.blob addr bytes
        have hmaps := refsIndex_eq_of_exprTableView_eq hblobbed.tables
        have hindex : blobbed.refsIndex.get? addr = some refIdx := by
          rw [hmaps]
          exact hpreseed'
        have hintern := run_internRef_hit compileEnv blockEnv blobbed addr refIdx
          hindex
        let root := blobbed.arena.nodes.size.toUInt64
        let finalState := allocState blobbed .leaf
        obtain ⟨hfinalCache, hextends, hgrowth, hnode⟩ :=
          arenaLeafFrame (before := state) (middle := blobbed) harena rfl rfl
            .leaf hleafRoom
        have hfinalCache' : ArenaCacheWF finalState := by
          dsimp [finalState]
          exact hfinalCache
        have hextends' : ArenaExtends state.arena finalState.arena := by
          dsimp [finalState]
          exact hextends
        have hnode' : finalState.arena.nodes[root.toNat]? = some .leaf := by
          dsimp [finalState, root]
          exact hnode
        refine ⟨root, finalState, ?_, hblobbed.alloc .leaf, hfinalCache',
          ⟨ArenaRel.lit hnode', hextends', ?_⟩⟩
        · rw [Ix.CompileM.compileExprNoSurgeryStep,
            run_bind compileEnv blockEnv state _ _,
            run_insertBlockBlob compileEnv blockEnv state addr bytes]
          simp only
          rw [run_bind compileEnv blockEnv blobbed _ _, hintern]
          simp only
          rw [run_bind compileEnv blockEnv blobbed _ _, run_allocArenaNode]
          rfl
        · change (allocState blobbed .leaf).arena.nodes.size ≤
            state.arena.nodes.size + exprArenaCost (.lit (.strVal value) hash)
          simpa [exprArenaCost] using hgrowth
  | @proj typeName field val hash hval =>
    cases hresolve : resolveConstAddr? compileEnv snapshot typeName with
    | none =>
      have hctxRef :
          (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
              typeName = none := by
        simp only [frozenRefCompileCtx]
        rw [hresolve]
        rfl
      simp [compileExprRef, hctxRef] at href
    | some addr =>
      cases hpreseed : snapshot.refsIndex.get? addr with
      | none =>
        have hctxRef :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                typeName = none := by
          simp only [frozenRefCompileCtx]
          rw [hresolve]
          change snapshot.refsIndex.get? addr = none
          exact hpreseed
        simp [compileExprRef, hctxRef] at href
      | some refIdx =>
        have hctxRef :
            (frozenRefCompileCtx compileEnv blockEnv snapshot).refIndex
                typeName = some refIdx := by
          simp only [frozenRefCompileCtx]
          rw [hresolve]
          change snapshot.refsIndex.get? addr = some refIdx
          exact hpreseed
        simp [compileExprRef, hctxRef] at href
        rcases href with ⟨valTarget, hvalRef, rfl⟩
        have hvalDepth : Ix.CompileM.exprCompileDepth val ≤ fuel := by
          simp only [Ix.CompileM.exprCompileDepth] at hdepth
          omega
        let nameState := state.compileName typeName
        have hnameState := hstate.compileName typeName
        have hnameArenaEq : nameState.arena = state.arena :=
          BlockState.compileName_arena state typeName
        have hnameCacheEq : nameState.exprCache = state.exprCache :=
          BlockState.compileName_exprCache state typeName
        have hnameCache : ArenaCacheWF nameState :=
          harena.of_frame hnameCacheEq (by
            rw [hnameArenaEq]
            exact ArenaExtends.refl state.arena)
        have hresolveName :
            resolveConstAddr? compileEnv nameState typeName = some addr := by
          rw [resolveConstAddr?_of_exprTableView_eq compileEnv
            hnameState.tables]
          exact hresolve
        have hmaps := refsIndex_eq_of_exprTableView_eq hnameState.tables
        have hindexName : nameState.refsIndex.get? addr = some refIdx := by
          rw [hmaps]
          exact hpreseed
        have hlookupRun := run_lookupConstAddr_resolved compileEnv blockEnv
          nameState typeName addr hresolveName
        have hinternRun := run_internRef_hit compileEnv blockEnv nameState addr
          refIdx hindexName
        have hvalRoom :
            nameState.arena.nodes.size + exprArenaCost val < UInt64.size := by
          rw [hnameArenaEq]
          simp only [exprArenaCost] at hroom
          omega
        obtain ⟨valRoot, valState, hvalRun, hvalState, hvalCache,
            hvalArena⟩ :=
          hrecur hvalDepth hval hnameState hnameCache hvalRoom hvalRef
        have hallocRoom : valState.arena.nodes.size < UInt64.size := by
          have hvalGrowth := hvalArena.growth
          rw [hnameArenaEq] at hvalGrowth
          simp only [exprArenaCost] at hroom
          omega
        let root := valState.arena.nodes.size.toUInt64
        let node : Ixon.ExprMetaData := .prj typeName.getHash valRoot
        let finalState := allocState valState node
        have hallocExtends : ArenaExtends valState.arena finalState.arena := by
          dsimp [finalState]
          exact allocState_arenaExtends valState node
        have hrootNode : finalState.arena.nodes[root.toNat]? = some node := by
          simpa [finalState, root] using allocState_root valState node hallocRoom
        have hrootRel :
            ArenaRel (.proj typeName field val hash) root finalState.arena :=
          .proj (hvalArena.rootRel.mono hallocExtends) hrootNode
        have hfinalCache : ArenaCacheWF finalState :=
          hvalCache.of_frame rfl hallocExtends
        have hfinalGrowth :
            finalState.arena.nodes.size ≤ state.arena.nodes.size +
              exprArenaCost (.proj typeName field val hash) := by
          have hvalGrowth := hvalArena.growth
          rw [hnameArenaEq] at hvalGrowth
          simp only [exprArenaCost]
          simp [finalState, node, allocState]
          omega
        refine ⟨root, finalState, ?_, hvalState.alloc node, hfinalCache,
          ⟨hrootRel,
            (by
              rw [← hnameArenaEq]
              exact ArenaExtends.trans hvalArena.arenaExtends hallocExtends),
            hfinalGrowth⟩⟩
        rw [Ix.CompileM.compileExprNoSurgeryStep,
          run_bind compileEnv blockEnv state _ _, run_compileName]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hlookupRun]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hinternRun]
        simp only
        rw [run_bind compileEnv blockEnv nameState _ _, hvalRun]
        simp only
        rw [run_bind compileEnv blockEnv valState _ _, run_allocArenaNode]
        rfl
  | @mdata data inner hash hdata hinner =>
    have hinnerRef :
        compileExprRef (frozenRefCompileCtx compileEnv blockEnv snapshot)
            inner = some target := by
      simpa [compileExprRef] using href
    have hinnerDepth : Ix.CompileM.exprCompileDepth inner ≤ fuel := by
      simp only [Ix.CompileM.exprCompileDepth] at hdepth
      omega
    obtain ⟨kvmap, hkvmapRef⟩ := hdata
    obtain ⟨metaState, hmetaRun, hmetaFrame⟩ :=
      compileKVMap_run_refines compileEnv blockEnv state hkvmapRef
    have hmetaState :
        FrozenExprStateWF compileEnv blockEnv levelSupport snapshot metaState :=
      hstate.of_metaFrame hmetaFrame
    have hmetaCache : ArenaCacheWF metaState :=
      harena.of_metaFrame hmetaFrame
    have hinnerRoom :
        metaState.arena.nodes.size + exprArenaCost inner < UInt64.size := by
      rw [hmetaFrame.arena]
      simp only [exprArenaCost] at hroom
      omega
    obtain ⟨innerRoot, innerState, hinnerRun, hinnerState, hinnerCache,
        hinnerArena⟩ :=
      hrecur hinnerDepth hinner hmetaState hmetaCache hinnerRoom hinnerRef
    have hallocRoom : innerState.arena.nodes.size < UInt64.size := by
      have hinnerGrowth := hinnerArena.growth
      simp only [exprArenaCost] at hroom
      rw [hmetaFrame.arena] at hinnerGrowth
      omega
    let root := innerState.arena.nodes.size.toUInt64
    let node : Ixon.ExprMetaData := .mdata #[kvmap] innerRoot
    let finalState := allocState innerState node
    have hallocExtends : ArenaExtends innerState.arena finalState.arena := by
      dsimp [finalState]
      exact allocState_arenaExtends innerState node
    have hrootNode : finalState.arena.nodes[root.toNat]? = some node := by
      simpa [finalState, root] using allocState_root innerState node hallocRoom
    have hrootRel :
        ArenaRel (.mdata data inner hash) root finalState.arena :=
      .mdata hkvmapRef (hinnerArena.rootRel.mono hallocExtends) hrootNode
    have hfinalCache : ArenaCacheWF finalState :=
      hinnerCache.of_frame rfl hallocExtends
    have hfinalGrowth :
        finalState.arena.nodes.size ≤ state.arena.nodes.size +
          exprArenaCost (.mdata data inner hash) := by
      have hinnerGrowth := hinnerArena.growth
      rw [hmetaFrame.arena] at hinnerGrowth
      simp only [exprArenaCost]
      simp [finalState, node, allocState]
      omega
    refine ⟨root, finalState, ?_, hinnerState.alloc node, hfinalCache,
      ⟨hrootRel,
        (by
          rw [← hmetaFrame.arena]
          exact ArenaExtends.trans hinnerArena.arenaExtends hallocExtends),
        hfinalGrowth⟩⟩
    rw [Ix.CompileM.compileExprNoSurgeryStep,
      run_bind compileEnv blockEnv state _ _, hmetaRun]
    simp only
    rw [run_bind compileEnv blockEnv metaState _ _, hinnerRun]
    simp only
    rw [run_bind compileEnv blockEnv innerState _ _, run_allocArenaNode]
    rfl

/-- The fuel-total production compiler refines the frozen reference compiler
on the complete recursive ordinary domain: structural nodes, arbitrary-level
constants, canonical sorts, literals, and projections. -/
theorem compileExprNoSurgeryFuel_ordinary_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {fuel : Nat} {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  induction fuel generalizing state source target with
  | zero =>
    have hpos := exprCompileDepth_pos source
    omega
  | succ fuel ih =>
    cases hlookup : state.exprCache.get? source with
    | some cached =>
      rcases cached with ⟨cachedTarget, cachedRoot⟩
      have hcachedRef := hstate.exprCache.sound hlookup
      have htarget : cachedTarget = target :=
        Option.some.inj (hcachedRef.symm.trans href)
      subst cachedTarget
      exact ⟨cachedRoot, state,
        compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
          source (target, cachedRoot) hlookup,
        hstate⟩
    | none =>
      obtain ⟨root, stepState, hstepRun, hstepState⟩ :=
        compileExprNoSurgeryStep_ordinary_refines compileEnv blockEnv snapshot
          hclosed hlevelFaithful fuel
          (fun hdepth hsource hstate href =>
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
      · exact hstepState.cache hexprFaithful hsource.ordinary href

theorem compileExprNoSurgery_run_ordinary_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgery source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  exact compileExprNoSurgeryFuel_ordinary_refines compileEnv blockEnv snapshot
    hclosed hlevelFaithful hexprFaithful (Nat.le_refl _) hsource hstate href

/-- Complete production ordinary-expression refinement in a surgery-free
environment, including recursive projections and arbitrary universe lists. -/
theorem compileExpr_run_ordinary_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExprNoSurgery_run_ordinary_refines compileEnv blockEnv snapshot
      hclosed hlevelFaithful hexprFaithful hsource hstate href
  refine ⟨root, state', ?_, hstate'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  exact hrun

/-- Complete ordinary compilation preserves the independent Lean4Lean value
assigned to the source expression. -/
theorem compileExpr_run_ordinary_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} {value : Lean4Lean.VExpr}
    (hordinary : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals source value)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        target value := by
  obtain ⟨root, state', hrun, hstate'⟩ :=
    compileExpr_run_ordinary_refines compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hordinary hstate href
  exact ⟨root, state', hrun, hstate',
    compileExprRef_value hctx hsource href⟩

/-- Fuel-total ordinary refinement with a structurally valid returned arena
root. The explicit capacity premise prevents `Nat.toUInt64` allocation-index
wraparound; cache hits only reduce the proved worst-case growth. -/
theorem compileExprNoSurgeryFuel_ordinary_arena_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {fuel : Nat} {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hdepth : Ix.CompileM.exprCompileDepth source ≤ fuel)
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgeryFuel fuel source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena := by
  induction fuel generalizing state source target with
  | zero =>
    have hpos := exprCompileDepth_pos source
    omega
  | succ fuel ih =>
    cases hlookup : state.exprCache.get? source with
    | some cached =>
      rcases cached with ⟨cachedTarget, cachedRoot⟩
      have hcachedRef := hstate.exprCache.sound hlookup
      have htarget : cachedTarget = target :=
        Option.some.inj (hcachedRef.symm.trans href)
      subst cachedTarget
      have hroot := harena.sound hlookup
      refine ⟨cachedRoot, state,
        compileExprNoSurgeryFuel_run_cached compileEnv blockEnv state fuel
          source (target, cachedRoot) hlookup,
        hstate, harena, ⟨hroot, ArenaExtends.refl state.arena, ?_⟩⟩
      have hcost := exprArenaCost_pos source
      omega
    | none =>
      obtain ⟨root, stepState, hstepRun, hstepState, hstepCache,
          hstepArena⟩ :=
        compileExprNoSurgeryStep_ordinary_arena_refines compileEnv blockEnv
          snapshot hclosed hlevelFaithful fuel
          (fun hdepth hsource hstate harena hroom href =>
            ih hdepth hsource hstate harena hroom href)
          hdepth hsource hstate harena hroom href
      let finalState := cacheState stepState source target root
      have hfinalState :
          FrozenExprStateWF compileEnv blockEnv levelSupport snapshot
            finalState :=
        hstepState.cache hexprFaithful hsource.ordinary href
      have hfinalCache : ArenaCacheWF finalState := by
        simpa [finalState, cacheState] using
          hstepCache.insert hexprFaithful hsource.ordinary hstepArena.rootRel
      have hfinalArena :
          ArenaCompileRel source root state.arena finalState.arena := by
        simpa [finalState, cacheState] using hstepArena
      refine ⟨root, finalState, ?_, hfinalState, hfinalCache, hfinalArena⟩
      rw [Ix.CompileM.compileExprNoSurgeryFuel.eq_2,
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

theorem compileExprNoSurgery_run_ordinary_arena_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExprNoSurgery source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena := by
  exact compileExprNoSurgeryFuel_ordinary_arena_refines compileEnv blockEnv
    snapshot hclosed hlevelFaithful hexprFaithful (Nat.le_refl _) hsource
    hstate harena hroom href

/-- Public surgery-free ordinary compilation returns both the canonical Ixon
expression and a structurally faithful presentation-arena root. -/
theorem compileExpr_run_ordinary_arena_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena := by
  obtain ⟨root, state', hrun, hstate', hcache', harena'⟩ :=
    compileExprNoSurgery_run_ordinary_arena_refines compileEnv blockEnv
      snapshot hclosed hlevelFaithful hexprFaithful hsource hstate harena
      hroom href
  refine ⟨root, state', ?_, hstate', hcache', harena'⟩
  rw [Ix.CompileM.compileExpr, run_bind compileEnv blockEnv state,
    run_getCompileEnv]
  simp only
  rw [hfree]
  exact hrun

/-- The strengthened public theorem exposes canonical value preservation and
the faithful presentation sidecar in one result. -/
theorem compileExpr_run_ordinary_arena_value
    {venv : Lean4Lean.VEnv} {sctx : SourceCtx} {catalog : Catalog}
    {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List Lean4Lean.VExpr}
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hctx : RefCompileCtxRel
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sctx catalog dctx)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr} {value : Lean4Lean.VExpr}
    (hordinary : SupportedOrdinaryExpr levelSupport source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (harena : ArenaCacheWF state)
    (hroom : state.arena.nodes.size + exprArenaCost source < UInt64.size)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals source value)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      ArenaCacheWF state' ∧
      ArenaCompileRel source root state.arena state'.arena ∧
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        target value := by
  obtain ⟨root, state', hrun, hstate', hcache', harena'⟩ :=
    compileExpr_run_ordinary_arena_refines compileEnv blockEnv snapshot hfree
      hclosed hlevelFaithful hexprFaithful hordinary hstate harena hroom href
  exact ⟨root, state', hrun, hstate', hcache', harena',
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
