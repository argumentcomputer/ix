import Ix.Compile.Verify.CompileState
import Ix.Compile.Verify.Reference
import Std.Data.HashMap.Lemmas

/-!
# Production universe-compiler refinement

`Ix.CompileM.compileUniv` is structurally recursive as of Lean 4.33, so its
equations are available to the kernel.  This module isolates the remaining
digest boundary for its memo table and relates successful cache entries to
the total `compileUnivRef` specification.

The Boolean equality on `Ix.Level` is equality of its stored root digest.  It
is an equivalence relation suitable for hash-map laws, but it is not globally
lawful structural equality.  `LevelKeyFaithfulOn` states exactly the finite
run support on which a digest hit may be converted to structural equality.
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

local instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

/-- Digest equality on levels is reflexive, symmetric, and transitive even
though it need not imply structural equality. -/
local instance : EquivBEq Ix.Level where
  rfl {level} := by
    change level.getHash == level.getHash
    exact BEq.rfl
  symm {a b} h := by
    change a.getHash == b.getHash at h
    change b.getHash == a.getHash
    have hhash : a.getHash = b.getHash := eq_of_beq h
    exact beq_of_eq hhash.symm
  trans {a b c} hleft hright := by
    change a.getHash == b.getHash at hleft
    change b.getHash == c.getHash at hright
    change a.getHash == c.getHash
    have hhashLeft : a.getHash = b.getHash := eq_of_beq hleft
    have hhashRight : b.getHash = c.getHash := eq_of_beq hright
    exact beq_of_eq (hhashLeft.trans hhashRight)

local instance : LawfulHashable Ix.Level where
  hash_eq left right h := by
    change hash left.getHash = hash right.getHash
    exact LawfulHashable.hash_eq left.getHash right.getHash h

/-- No level in the finite support of this compiler run has the same digest
as a structurally different queried level.  Only the stored/inserted side is
required to be in the support, which is sufficient for hash-map lookup. -/
def LevelKeyFaithfulOn (support : Ix.Level → Prop) : Prop :=
  ∀ {stored queried}, support stored → (stored == queried) = true →
    stored = queried

/-- The support contains every recursive child that universe compilation can
visit. -/
structure LevelSupportClosed (support : Ix.Level → Prop) : Prop where
  succ {level hash} : support (.succ level hash) → support level
  maxLeft {left right hash} : support (.max left right hash) → support left
  maxRight {left right hash} : support (.max left right hash) → support right
  imaxLeft {left right hash} : support (.imax left right hash) → support left
  imaxRight {left right hash} : support (.imax left right hash) → support right

/-- The positional parameter choice made by production `compileUniv`. -/
def univParamIndex (univCtx : List Ix.Name) (name : Ix.Name) : Option UInt64 :=
  (univCtx.idxOf? name).map Nat.toUInt64

/-- Every successful universe-cache lookup is on the run support and agrees
with the total reference compiler under the fixed parameter assignment. -/
structure UnivCacheWF (paramIndex : Ix.Name → Option UInt64)
    (support : Ix.Level → Prop) (state : Ix.CompileM.BlockState) : Prop where
  supported : ∀ {level u}, state.univCache.get? level = some u → support level
  sound : ∀ {level u}, state.univCache.get? level = some u →
    compileUnivRef paramIndex level = some u

/-- The canonical-universe memo returns exactly the deterministic
`Ixon.canonUniv` result for every cached raw universe. -/
structure CanonUnivCacheWF (state : Ix.CompileM.BlockState) : Prop where
  sound : ∀ {raw canon}, state.canonUnivCache.get? raw = some canon →
    canon = Ixon.canonUniv raw

theorem CanonUnivCacheWF.empty :
    CanonUnivCacheWF (default : Ix.CompileM.BlockState) := by
  constructor
  intro raw canon h
  change ({} : Std.HashMap Ixon.Univ Ixon.Univ).get? raw = some canon at h
  simp at h

theorem CanonUnivCacheWF.of_cache_eq {before after : Ix.CompileM.BlockState}
    (hbefore : CanonUnivCacheWF before)
    (heq : after.canonUnivCache = before.canonUnivCache) :
    CanonUnivCacheWF after := by
  constructor
  intro raw canon h
  exact hbefore.sound (heq ▸ h)

theorem CanonUnivCacheWF.insert {state : Ix.CompileM.BlockState}
    (hstate : CanonUnivCacheWF state) (raw : Ixon.Univ) :
    CanonUnivCacheWF
      { state with
        canonUnivCache := state.canonUnivCache.insert raw (Ixon.canonUniv raw) } := by
  constructor
  intro queried found hfound
  change (state.canonUnivCache.insert raw (Ixon.canonUniv raw)).get? queried =
    some found at hfound
  simp only [Std.HashMap.get?_insert] at hfound
  split at hfound
  next heq =>
    have hsame : raw = queried := eq_of_beq heq
    subst queried
    exact (Option.some.inj hfound).symm
  next => exact hstate.sound hfound

theorem UnivCacheWF.empty (paramIndex : Ix.Name → Option UInt64)
    (support : Ix.Level → Prop) :
    UnivCacheWF paramIndex support (default : Ix.CompileM.BlockState) := by
  constructor <;> intro level u h
  · change ({} : Std.HashMap Ix.Level Ixon.Univ).get? level = some u at h
    simp at h
  · change ({} : Std.HashMap Ix.Level Ixon.Univ).get? level = some u at h
    simp at h

theorem UnivCacheWF.of_cache_eq {paramIndex : Ix.Name → Option UInt64}
    {support : Ix.Level → Prop} {before after : Ix.CompileM.BlockState}
    (hbefore : UnivCacheWF paramIndex support before)
    (heq : after.univCache = before.univCache) :
    UnivCacheWF paramIndex support after := by
  constructor <;> intro level u h
  · exact hbefore.supported (heq ▸ h)
  · exact hbefore.sound (heq ▸ h)

/-- Inserting a reference-correct supported level preserves cache
correctness.  This is the only place where a digest hit is converted to
structural equality. -/
theorem UnivCacheWF.insert {paramIndex : Ix.Name → Option UInt64}
    {support : Ix.Level → Prop} {state : Ix.CompileM.BlockState}
    (hstate : UnivCacheWF paramIndex support state)
    (hfaithful : LevelKeyFaithfulOn support) {level : Ix.Level}
    (hlevel : support level) {u : Ixon.Univ}
    (hcompile : compileUnivRef paramIndex level = some u) :
    UnivCacheWF paramIndex support
      (state.cacheUniv level u) := by
  constructor
  · intro queried found hfound
    change (state.univCache.insert level u).get? queried = some found at hfound
    simp only [Std.HashMap.get?_insert] at hfound
    split at hfound
    next heq =>
      have hsame : level = queried := hfaithful hlevel heq
      simpa [← hsame] using hlevel
    next hne => exact hstate.supported hfound
  · intro queried found hfound
    change (state.univCache.insert level u).get? queried = some found at hfound
    simp only [Std.HashMap.get?_insert] at hfound
    split at hfound
    next heq =>
      have hsame : level = queried := hfaithful hlevel heq
      subst queried
      have hvalue : found = u := (Option.some.inj hfound).symm
      subst found
      exact hcompile
    next hne => exact hstate.sound hfound

private theorem run_getBlockState (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getBlockState = .ok (state, state) := by
  rfl

private theorem run_getBlockEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
      Ix.CompileM.getBlockEnv = .ok (blockEnv, state) := by
  rfl

private theorem run_cacheUniv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (level : Ix.Level) (u : Ixon.Univ) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (do
      Ix.CompileM.modifyBlockState fun current => current.cacheUniv level u
      pure u) = .ok (u, state.cacheUniv level u) := by
  rfl

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

private def cacheCanonState (state : Ix.CompileM.BlockState)
    (raw : Ixon.Univ) : Ix.CompileM.BlockState :=
  { state with
    canonUnivCache := state.canonUnivCache.insert raw (Ixon.canonUniv raw) }

/-- The production canonical-universe memo computes the deterministic
canonical representative and changes neither primary expression tables nor
the expression/universe compilation caches. -/
theorem canonUnivCached_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {state : Ix.CompileM.BlockState}
    (hstate : CanonUnivCacheWF state) (raw : Ixon.Univ) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.canonUnivCached raw) =
        .ok (Ixon.canonUniv raw, state') ∧
      CanonUnivCacheWF state' ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache := by
  cases hlookup : state.canonUnivCache.get? raw with
  | some cached =>
    have hvalue : cached = Ixon.canonUniv raw := hstate.sound hlookup
    subst cached
    refine ⟨state, ?_, hstate, rfl, rfl, rfl⟩
    rw [Ix.CompileM.canonUnivCached,
      run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
      run_getBlockState]
    simp only
    rw [hlookup]
    rfl
  | none =>
    let state' := cacheCanonState state raw
    refine ⟨state', ?_, ?_, rfl, rfl, rfl⟩
    · rw [Ix.CompileM.canonUnivCached,
        run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
        run_getBlockState]
      simp only
      rw [hlookup]
      rfl
    · simpa [state', cacheCanonState] using hstate.insert raw

private theorem run_internUniv_hit
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (u : Ixon.Univ) (idx : UInt64)
    (hindex : state.univsIndex.get? u = some idx) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internUniv u) = .ok (idx, state) := by
  change Except.ok ((state.internUniv u).2, (state.internUniv u).1) =
    Except.ok (idx, state)
  rw [Ix.CompileM.BlockState.internUniv, hindex]

private theorem internMetaUniv_run_frame
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (raw : Ixon.Univ) :
    ∃ idx state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internMetaUniv raw) = .ok (idx, state') ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache := by
  cases hlookup : state.metaUnivsIndex.get? raw with
  | some slot =>
    refine ⟨state.univs.size.toUInt64 + slot, state, ?_, rfl, rfl, rfl, rfl⟩
    change Except.ok ((state.internMetaUniv raw).2,
      (state.internMetaUniv raw).1) = _
    rw [Ix.CompileM.BlockState.internMetaUniv, hlookup]
  | none =>
    let slot := state.metaUnivs.size.toUInt64
    let state' : Ix.CompileM.BlockState :=
      { state with
        metaUnivs := state.metaUnivs.push raw
        metaUnivsIndex := state.metaUnivsIndex.insert raw slot }
    refine ⟨state.univs.size.toUInt64 + slot, state', ?_, rfl, rfl, rfl, rfl⟩
    change Except.ok ((state.internMetaUniv raw).2,
      (state.internMetaUniv raw).1) = _
    rw [Ix.CompileM.BlockState.internMetaUniv, hlookup]

/-- A production cache hit is observationally a pure successful return; no
block-state field changes. -/
theorem compileUniv_run_cached (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (level : Ix.Level) (u : Ixon.Univ)
    (hcache : state.univCache.get? level = some u) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv level) = .ok (u, state) := by
  rw [Ix.CompileM.compileUniv.eq_1]
  rw [run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hcache]
  rfl

private theorem compileUniv_run_zero_miss
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (hash : Address)
    (hmissing : state.univCache.get? (.zero hash) = none) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv (.zero hash)) =
      .ok (.zero, state.cacheUniv (.zero hash) .zero) := by
  rw [Ix.CompileM.compileUniv.eq_1,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing]
  exact run_cacheUniv compileEnv blockEnv state (.zero hash) .zero

private theorem compileUniv_run_succ_miss
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (level : Ix.Level) (hash : Address)
    (hmissing : state.univCache.get? (.succ level hash) = none)
    {u : Ixon.Univ} {state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compileUniv level) = .ok (u, state')) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv (.succ level hash)) =
      .ok (.succ u, state'.cacheUniv (.succ level hash) (.succ u)) := by
  rw [Ix.CompileM.compileUniv.eq_1,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing]
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    let inner ← Ix.CompileM.compileUniv level
    Ix.CompileM.modifyBlockState fun current =>
      current.cacheUniv (.succ level hash) (Ixon.Univ.succ inner)
    pure (Ixon.Univ.succ inner)) = _
  rw [run_bind compileEnv blockEnv state (Ix.CompileM.compileUniv level), hrun]
  simp only
  exact run_cacheUniv compileEnv blockEnv state' (.succ level hash) (.succ u)

private theorem compileUniv_run_max_miss
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (left right : Ix.Level) (hash : Address)
    (hmissing : state.univCache.get? (.max left right hash) = none)
    {leftU rightU : Ixon.Univ}
    {leftState rightState : Ix.CompileM.BlockState}
    (hleft : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compileUniv left) = .ok (leftU, leftState))
    (hright : Ix.CompileM.CompileM.run compileEnv blockEnv leftState
      (Ix.CompileM.compileUniv right) = .ok (rightU, rightState)) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv (.max left right hash)) =
      .ok (.max leftU rightU,
        rightState.cacheUniv (.max left right hash) (.max leftU rightU)) := by
  rw [Ix.CompileM.compileUniv.eq_1,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing]
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    let leftU ← Ix.CompileM.compileUniv left
    let rightU ← Ix.CompileM.compileUniv right
    Ix.CompileM.modifyBlockState fun current =>
      current.cacheUniv (.max left right hash) (Ixon.Univ.max leftU rightU)
    pure (Ixon.Univ.max leftU rightU)) = _
  rw [run_bind compileEnv blockEnv state (Ix.CompileM.compileUniv left), hleft]
  simp only
  rw [run_bind compileEnv blockEnv leftState (Ix.CompileM.compileUniv right),
    hright]
  simp only
  exact run_cacheUniv compileEnv blockEnv rightState
    (.max left right hash) (.max leftU rightU)

private theorem compileUniv_run_imax_miss
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (left right : Ix.Level) (hash : Address)
    (hmissing : state.univCache.get? (.imax left right hash) = none)
    {leftU rightU : Ixon.Univ}
    {leftState rightState : Ix.CompileM.BlockState}
    (hleft : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.compileUniv left) = .ok (leftU, leftState))
    (hright : Ix.CompileM.CompileM.run compileEnv blockEnv leftState
      (Ix.CompileM.compileUniv right) = .ok (rightU, rightState)) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv (.imax left right hash)) =
      .ok (.imax leftU rightU,
        rightState.cacheUniv (.imax left right hash) (.imax leftU rightU)) := by
  rw [Ix.CompileM.compileUniv.eq_1,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing]
  change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
    let leftU ← Ix.CompileM.compileUniv left
    let rightU ← Ix.CompileM.compileUniv right
    Ix.CompileM.modifyBlockState fun current =>
      current.cacheUniv (.imax left right hash) (Ixon.Univ.imax leftU rightU)
    pure (Ixon.Univ.imax leftU rightU)) = _
  rw [run_bind compileEnv blockEnv state (Ix.CompileM.compileUniv left), hleft]
  simp only
  rw [run_bind compileEnv blockEnv leftState (Ix.CompileM.compileUniv right),
    hright]
  simp only
  exact run_cacheUniv compileEnv blockEnv rightState
    (.imax left right hash) (.imax leftU rightU)

private theorem compileUniv_run_param_miss
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (name : Ix.Name) (hash : Address)
    (hmissing : state.univCache.get? (.param name hash) = none)
    {idx : Nat} (hidx : blockEnv.univCtx.idxOf? name = some idx) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileUniv (.param name hash)) =
      .ok (.var idx.toUInt64,
        state.cacheUniv (.param name hash) (.var idx.toUInt64)) := by
  rw [Ix.CompileM.compileUniv.eq_1,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  rw [hmissing,
    run_bind compileEnv blockEnv state Ix.CompileM.getBlockEnv,
    run_getBlockEnv]
  simp only
  rw [hidx]
  exact run_cacheUniv compileEnv blockEnv state
    (.param name hash) (.var idx.toUInt64)

private theorem compileUniv_cached_refines
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    {support : Ix.Level → Prop} {state : Ix.CompileM.BlockState}
    {level : Ix.Level} {target cached : Ixon.Univ}
    (hstate : UnivCacheWF (univParamIndex blockEnv.univCtx) support state)
    (href : compileUnivRef (univParamIndex blockEnv.univCtx) level =
      some target)
    (hcached : state.univCache.get? level = some cached) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileUniv level) = .ok (target, state') ∧
      UnivCacheWF (univParamIndex blockEnv.univCtx) support state' ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.canonUnivCache = state.canonUnivCache := by
  have hvalue : cached = target :=
    Option.some.inj ((hstate.sound hcached).symm.trans href)
  subst target
  exact ⟨state, compileUniv_run_cached compileEnv blockEnv state level cached
    hcached, hstate, rfl, rfl, rfl⟩

/-- Production universe compilation refines the total reference compiler.
Every successful reference input runs successfully to the same positional
universe, and the production memo remains correct.  The only non-structural
premise is finite-support digest faithfulness for the levels this run may
insert. -/
theorem compileUniv_run_refines
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    {support : Ix.Level → Prop}
    (hclosed : LevelSupportClosed support)
    (hfaithful : LevelKeyFaithfulOn support)
    {state : Ix.CompileM.BlockState} {level : Ix.Level}
    {target : Ixon.Univ} (hlevel : support level)
    (hstate : UnivCacheWF (univParamIndex blockEnv.univCtx) support state)
    (href : compileUnivRef (univParamIndex blockEnv.univCtx) level =
      some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileUniv level) = .ok (target, state') ∧
      UnivCacheWF (univParamIndex blockEnv.univCtx) support state' ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.canonUnivCache = state.canonUnivCache := by
  induction level generalizing state target with
  | zero hash =>
    cases hlookup : state.univCache.get? (.zero hash) with
    | some cached =>
      exact compileUniv_cached_refines compileEnv blockEnv hstate href hlookup
    | none =>
      simp [compileUnivRef] at href
      subst target
      refine ⟨state.cacheUniv (.zero hash) .zero,
        compileUniv_run_zero_miss compileEnv blockEnv state hash hlookup,
        hstate.insert hfaithful hlevel (by simp [compileUnivRef]), ?_, ?_, ?_⟩
      · rfl
      · rfl
      · rfl
  | succ level hash ih =>
    cases hlookup : state.univCache.get? (.succ level hash) with
    | some cached =>
      exact compileUniv_cached_refines compileEnv blockEnv hstate href hlookup
    | none =>
      simp [compileUnivRef] at href
      rcases href with ⟨u, hu, rfl⟩
      obtain ⟨state', hrun, hstate', hview, hcache, hcanonCache⟩ :=
        ih (hclosed.succ hlevel) hstate hu
      refine ⟨state'.cacheUniv (.succ level hash) (.succ u),
        compileUniv_run_succ_miss compileEnv blockEnv state level hash
          hlookup hrun,
        hstate'.insert hfaithful hlevel (by simp [compileUnivRef, hu]),
        ?_, ?_, ?_⟩
      · simpa using hview
      · simpa using hcache
      · simpa using hcanonCache
  | max left right hash ihLeft ihRight =>
    cases hlookup : state.univCache.get? (.max left right hash) with
    | some cached =>
      exact compileUniv_cached_refines compileEnv blockEnv hstate href hlookup
    | none =>
      simp [compileUnivRef] at href
      rcases href with ⟨leftU, hleft, rightU, hright, rfl⟩
      obtain ⟨leftState, hleftRun, hleftState, hleftView, hleftCache,
          hleftCanonCache⟩ :=
        ihLeft (hclosed.maxLeft hlevel) hstate hleft
      obtain ⟨rightState, hrightRun, hrightState, hrightView, hrightCache,
          hrightCanonCache⟩ :=
        ihRight (hclosed.maxRight hlevel) hleftState hright
      refine ⟨rightState.cacheUniv (.max left right hash)
          (.max leftU rightU),
        compileUniv_run_max_miss compileEnv blockEnv state left right hash
          hlookup hleftRun hrightRun,
        hrightState.insert hfaithful hlevel (by
          simp [compileUnivRef, hleft, hright]), ?_, ?_, ?_⟩
      · simpa using hrightView.trans hleftView
      · simpa using hrightCache.trans hleftCache
      · simpa using hrightCanonCache.trans hleftCanonCache
  | imax left right hash ihLeft ihRight =>
    cases hlookup : state.univCache.get? (.imax left right hash) with
    | some cached =>
      exact compileUniv_cached_refines compileEnv blockEnv hstate href hlookup
    | none =>
      simp [compileUnivRef] at href
      rcases href with ⟨leftU, hleft, rightU, hright, rfl⟩
      obtain ⟨leftState, hleftRun, hleftState, hleftView, hleftCache,
          hleftCanonCache⟩ :=
        ihLeft (hclosed.imaxLeft hlevel) hstate hleft
      obtain ⟨rightState, hrightRun, hrightState, hrightView, hrightCache,
          hrightCanonCache⟩ :=
        ihRight (hclosed.imaxRight hlevel) hleftState hright
      refine ⟨rightState.cacheUniv (.imax left right hash)
          (.imax leftU rightU),
        compileUniv_run_imax_miss compileEnv blockEnv state left right hash
          hlookup hleftRun hrightRun,
        hrightState.insert hfaithful hlevel (by
          simp [compileUnivRef, hleft, hright]), ?_, ?_, ?_⟩
      · simpa using hrightView.trans hleftView
      · simpa using hrightCache.trans hleftCache
      · simpa using hrightCanonCache.trans hleftCanonCache
  | param name hash =>
    cases hlookup : state.univCache.get? (.param name hash) with
    | some cached =>
      exact compileUniv_cached_refines compileEnv blockEnv hstate href hlookup
    | none =>
      cases hidx : blockEnv.univCtx.idxOf? name with
      | none => simp [compileUnivRef, univParamIndex, hidx] at href
      | some idx =>
        simp [compileUnivRef, univParamIndex, hidx] at href
        subst target
        refine ⟨state.cacheUniv (.param name hash) (.var idx.toUInt64),
          compileUniv_run_param_miss compileEnv blockEnv state name hash
            hlookup hidx,
          hstate.insert hfaithful hlevel (by
            simp [compileUnivRef, univParamIndex, hidx]), ?_, ?_, ?_⟩
        · rfl
        · rfl
        · rfl
  | mvar name hash =>
    simp [compileUnivRef] at href

/-- With the canonical primary universe already present in the preseeded
table, the complete production level-index operation returns that frozen
index, preserves both universe memos, and cannot trigger the post-preseed
growth tripwire. -/
theorem compileAndInternUnivCanon_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : Ix.Level → Prop}
    (hclosed : LevelSupportClosed support)
    (hfaithful : LevelKeyFaithfulOn support)
    {state : Ix.CompileM.BlockState} {level : Ix.Level}
    {raw : Ixon.Univ} {idx : UInt64} (hlevel : support level)
    (huniv : UnivCacheWF (univParamIndex blockEnv.univCtx) support state)
    (hcanon : CanonUnivCacheWF state)
    (href : compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw)
    (hindex : state.univsIndex.get? (Ixon.canonUniv raw) = some idx) :
    ∃ original? state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileAndInternUnivCanon level) =
        .ok ((idx, original?), state') ∧
      UnivCacheWF (univParamIndex blockEnv.univCtx) support state' ∧
      CanonUnivCacheWF state' ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache := by
  obtain ⟨univState, hunivRun, hunivState, hunivView, hunivExprCache,
      hunivCanonCache⟩ :=
    compileUniv_run_refines compileEnv blockEnv hclosed hfaithful hlevel
      huniv href
  have hunivCanon : CanonUnivCacheWF univState :=
    hcanon.of_cache_eq hunivCanonCache
  obtain ⟨canonState, hcanonRun, hcanonState, hcanonView,
      hcanonExprCache, hcanonUnivCache⟩ :=
    canonUnivCached_run_refines compileEnv blockEnv hunivCanon raw
  have hunivState' :
      UnivCacheWF (univParamIndex blockEnv.univCtx) support canonState :=
    hunivState.of_cache_eq hcanonUnivCache
  have hview : exprTableView canonState = exprTableView state :=
    hcanonView.trans hunivView
  have hexprCache : canonState.exprCache = state.exprCache :=
    hcanonExprCache.trans hunivExprCache
  have hindex' :
      canonState.univsIndex.get? (Ixon.canonUniv raw) = some idx := by
    have hmaps := congrArg ExprTableView.univsIndex hview
    change canonState.univsIndex = state.univsIndex at hmaps
    rw [hmaps]
    exact hindex
  have hintern := run_internUniv_hit compileEnv blockEnv canonState
    (Ixon.canonUniv raw) idx hindex'
  cases hsame : Ixon.canonUniv raw == raw with
  | true =>
    refine ⟨none, canonState, ?_, hunivState', hcanonState, hview,
      hexprCache⟩
    rw [Ix.CompileM.compileAndInternUnivCanon,
      run_bind compileEnv blockEnv state _ _, hunivRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, hcanonRun]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp only
    rw [run_bind compileEnv blockEnv canonState _ _, hintern]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp [hsame]
    rfl
  | false =>
    obtain ⟨original, finalState, horiginalRun, horiginalView,
        horiginalExprCache, horiginalUnivCache, horiginalCanonCache⟩ :=
      internMetaUniv_run_frame compileEnv blockEnv canonState raw
    refine ⟨some original, finalState, ?_,
      hunivState'.of_cache_eq horiginalUnivCache,
      hcanonState.of_cache_eq horiginalCanonCache,
      horiginalView.trans hview, horiginalExprCache.trans hexprCache⟩
    rw [Ix.CompileM.compileAndInternUnivCanon,
      run_bind compileEnv blockEnv state _ _, hunivRun]
    simp only
    rw [run_bind compileEnv blockEnv univState _ _, hcanonRun]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp only
    rw [run_bind compileEnv blockEnv canonState _ _, hintern]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp only
    rw [run_bind compileEnv blockEnv canonState Ix.CompileM.getBlockState,
      run_getBlockState]
    simp [hsame]
    change Ix.CompileM.CompileM.run compileEnv blockEnv canonState (do
      let original ← Ix.CompileM.internMetaUniv raw
      pure (idx, some original)) = _
    rw [run_bind compileEnv blockEnv canonState _ _, horiginalRun]
    rfl

/-- The production result therefore has the independent Lean4Lean universe
value assigned to the named source level. -/
theorem compileUniv_run_value
    (compileEnv : Ix.CompileM.CompileEnv) (blockEnv : Ix.CompileM.BlockEnv)
    {support : Ix.Level → Prop}
    (hclosed : LevelSupportClosed support)
    (hfaithful : LevelKeyFaithfulOn support)
    {state : Ix.CompileM.BlockState} {level : Ix.Level}
    {target : Ixon.Univ} (hlevel : support level)
    (hstate : UnivCacheWF (univParamIndex blockEnv.univCtx) support state)
    (href : compileUnivRef (univParamIndex blockEnv.univCtx) level =
      some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileUniv level) = .ok (target, state') ∧
      UnivCacheWF (univParamIndex blockEnv.univCtx) support state' ∧
      sourceUnivValue (univParamIndex blockEnv.univCtx) level =
        some (univToVLevel target) := by
  obtain ⟨state', hrun, hstate', _, _, _⟩ := compileUniv_run_refines
    compileEnv blockEnv hclosed hfaithful hlevel hstate href
  exact ⟨state', hrun, hstate', compileUnivRef_value href⟩

end Ix.Compile.Verify
