module

public import Ix.Tc.Infer

/-!
Mirror: crates/kernel/src/def_eq.rs

Multi-tier definitional equality (lean4lean shape):
1. quick structural (hash / binder common-fvar opening)
1b. eager Bool.true reduction; 1c. string-literal expansion **before any
    whnf**; 1d. cheap whnf-core then cheap whnf-no-delta passes
3. proof irrelevance (before delta), with the `isPropCache`
4. iterative lazy delta with ReducibilityHints ranking, tryUnfoldProjApp,
   and the same-head-spine attempt whose failures populate the
   `defEqFailure` negative cache — ONLY there (generalizing it is a
   completeness bug)
4b. post-delta structural congruence (Const/Var/Prj with proj-delta loop)
4c. second structural pass via `whnfCore` — deliberately NOT full whnf
4d. app-spine comparison
5. full structural + nat-literal bridging + eta + string expansion +
   struct-eta + unit-like + proof irrelevance

Cache discipline at the entry point: cheap-mode `false` goes only to the
cheap cache; cheap `true` promotes to the full cache and the EquivManager
(monotone-sound). Fuel is charged only after the O(1) exits.
-/

public section
@[expose] section

namespace Ix.Tc

/-- Lazy-delta single-step outcome. -/
inductive LazyDeltaStep where
  | equal
  | continue'
  | unknown
  deriving BEq, Repr, Inhabited

/-- Result of the bounded Tier-4 delta loop: either a final equality answer,
    or the pair on which the post-delta tiers must continue. -/
inductive LazyDeltaLoopResult (m : Mode) where
  | answer (result : Bool)
  | stopped (a b : KExpr m)

/-- Canonically ordered address pair (byte-lexicographic). -/
def canonicalPair (a b : Address) : Address × Address :=
  if a.cmpBytes b != .gt then (a, b) else (b, a)

/-- Canonical key for the narrow same-head rejection cache. -/
def defEqFailureKey (left right : KExpr m) (ctxAddr : Address) :
    Address × Address × Address :=
  ((canonicalPair left.addr right.addr).1,
    (canonicalPair left.addr right.addr).2, ctxAddr)

/-- Local recursive-fuel slice for one non-Regular same-head attempt. -/
def sameHeadSpeculationAttemptFuel : UInt64 := 4096

/-- Do not begin a fresh non-Regular same-head attempt after the enclosing
constant check has already consumed this much recursive fuel. Nested attempts
inherit the active local slice. -/
def sameHeadSpeculationStartFuel : UInt64 := 16384

/-- Head constant of an expression or app spine. -/
def headConstId (e : KExpr m) : Option (KId m) :=
  match e with
  | .const id _ _ => some id
  | .app .. =>
    match e.collectSpine with
    | (.const id _ _, _) => some id
    | _ => none
  | _ => none

namespace RecM

/-! ### Non-recursive definitional-equality helpers -/

/-- Lexicographic rank comparison ((class, height) tuples). -/
def compareRank (a b : Nat × Nat) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

def isNatLike (e : KExpr m) : RecM m Bool := do
  let p ← prims
  match e with
  | .nat .. => return true
  | .const id _ _ => return id.addr == p.natZero.addr
  | .app f _ _ =>
    match f with
    | .const id _ _ => return id.addr == p.natSucc.addr
    | _ => return false
  | _ => return false

def isNatZero (e : KExpr m) : RecM m Bool := do
  let p ← prims
  match e with
  | .nat v _ _ => return v == 0
  | .const id _ _ => return id.addr == p.natZero.addr
  | _ => return false

def natSuccOf (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let p ← prims
  match e with
  | .nat v _ _ =>
    if v == 0 then
      return none
    return some (← TcM.intern (natExprFromValue (v - 1) : KExpr m))
  | .app f arg _ =>
    match f with
    | .const id _ _ =>
      if id.addr == p.natSucc.addr then
        return some arg
      return none
    | _ => return none
  | _ => return none

/-- Allocation-free check that `e` could decompose to `base + offset`:
    a Nat literal, `Nat.zero`/`Nat.succ`, or an app whose head constant is
    `Nat.succ`/`Nat.add`. Walks the app chain — no spine. -/
def natOffsetCandidate (p : Primitives m) : KExpr m → Bool
  | .nat .. => true
  | .const id _ _ =>
    id.addr == p.natZero.addr || id.addr == p.natSucc.addr
      || id.addr == p.natAdd.addr
  | .app f _ _ => natOffsetCandidate p f
  | _ => false

def isBoolTrue (e : KExpr m) : RecM m Bool := do
  match e with
  | .const id us _ =>
    return us.isEmpty && id.addr == (← prims).boolTrue.addr
  | _ => return false

/-- Eager Bool reduction is unconditional for closed syntax and otherwise
follows the caller's explicit eager-reduction marker. -/
def boolTrueReductionAllowed (e : KExpr m) : RecM m Bool := do
  if !e.hasFVars then
    return true
  return (← get).eagerReduce

/-- Normalize a candidate and classify the resulting WHNF as `Bool.true`. -/
def whnfIsBoolTrue (e : KExpr m) : RecM m Bool := do
  isBoolTrue (← whnf e)

/-- Whether either side is syntactically a compact String literal. -/
def hasStringLiteralPair (a b : KExpr m) : Bool :=
  (match a with | .str .. => true | _ => false) ||
    (match b with | .str .. => true | _ => false)

/-- Is the constant delta-reducible (Definition/Theorem)? -/
def isDelta (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.defn (kind := kind) ..) =>
    match kind with
    | .defn | .thm => return true
    | .opaq => return false
  | _ => return false

/-- Classify the head constant of an expression as delta-reducible.  A
non-constant head is an immediate miss. -/
def classifyDeltaHead (e : KExpr m) : RecM m Bool :=
  match headConstId e with
  | some id => isDelta id
  | none => pure false

/-- Regular reducibility hints retain the unbounded same-head fast path. -/
def isRegular (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.defn (hints := .regular _) ..) => return true
  | _ => return false

/-- Reducibility rank `(class, height)`, lexicographic; higher unfolds
    first. Opaque/Theorem/unknown `(0,0)`; `Regular h` `(1,h)`;
    `Abbrev` `(2,0)`. -/
def defRankId (id : KId m) : RecM m (Nat × Nat) := do
  match (← TcM.tryGetConst id) with
  | some (.defn (kind := kind) (hints := hints) ..) =>
    match kind with
    | .opaq | .thm => return (0, 0)
    | .defn =>
      match hints with
      | .opaque => return (0, 0)
      | .regular h => return (1, h.toNat)
      | .abbrev => return (2, 0)
  | _ => return (0, 0)

/-- Read the reducibility rank of an optional head constant.  The sentinel
rank is retained for the syntactically headless case. -/
def rankDeltaHead (head : Option (KId m)) : RecM m (Nat × Nat) :=
  match head with
  | some id => defRankId id
  | none => pure (255, 4294967295)

mutual

/-- Definitional equality entry point: fast paths, equiv-manager, caches
    (with cheap-mode routing), fuel/depth accounting, then the tiers. -/
def isDefEq (a b : KExpr m) : RecM m Bool := do
  TcM.stepTrace (m := m) "deq" fun _ =>
    s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}"
  TcM.bumpStats (m := m) fun s => { s with deqCalls := s.deqCalls + 1 }
  if a.addr == b.addr then
    -- Hashes are alpha-invariant in both modes; this is the only
    -- structural alpha-equivalence fast path needed.
    return true
  let eqCtx ← TcM.defEqCtxKey a b
  let eqLbr := max a.lbr b.lbr
  let aKey : EqKey := ⟨a.addr, eqCtx, eqLbr, a.lbr⟩
  let bKey : EqKey := ⟨b.addr, eqCtx, eqLbr, b.lbr⟩
  let isEq ← TcM.withEquiv (m := m) (·.isEquiv aKey bKey)
  if isEq then
    return true
  let (lo, hi) := canonicalPair a.addr b.addr
  let cacheKey := (lo, hi, eqCtx)
  let cheapMode := (← get).cheapRecursionDepth > 0
  if let some cached := (← get).env.defEqCache[cacheKey]? then
    if cheapMode then
      modify fun s => { s with env := { s.env with
        defEqCheapCache := s.env.defEqCheapCache.insert cacheKey cached } }
    if cached then
      modify fun s => { s with
        equivManager := s.equivManager.addEquiv aKey bKey }
    return cached
  if cheapMode then
    if let some cached := (← get).env.defEqCheapCache[cacheKey]? then
      if cached then
        modify fun s => { s with
          env := { s.env with
            defEqCache := s.env.defEqCache.insert cacheKey true }
          equivManager := s.equivManager.addEquiv aKey bKey }
      return cached
  isDefEqAfterDirectCacheMiss a b eqCtx aKey bKey cacheKey cheapMode

/-- Guarded equivalence-root probe after both direct DefEq cache partitions
miss. Keeping this as a production seam lets verification cover the exact
remaining program without duplicating reducer control flow. -/
def isDefEqAfterDirectCacheMiss (a b : KExpr m) (eqCtx : Address)
    (aKey bKey : EqKey) (cacheKey : Address × Address × Address)
    (cheapMode : Bool) : RecM m Bool := do
  -- Equiv-root second chance: probe (root a, root b).
  let (aRoot?, bRoot?) ← TcM.withEquiv (m := m) fun em =>
    let (aRoot?, em) := em.findRootKey aKey
    let (bRoot?, em) := em.findRootKey bKey
    ((aRoot?, bRoot?), em)
  if let (some aRoot, some bRoot) := (aRoot?, bRoot?) then
    if aRoot != aKey || bRoot != bKey then
      -- A representative can have a different intrinsic radius from the
      -- original expression.  The root cache key reuses `eqCtx`, so probe it
      -- only when both representatives retain that exact cache scope.
      if aRoot.rootCacheScopeMatches bRoot eqCtx (max a.lbr b.lbr) then
        let (rlo, rhi) := canonicalPair aRoot.exprAddr bRoot.exprAddr
        let rootCacheKey := (rlo, rhi, eqCtx)
        let cached? : Option (Bool × Bool) ←
          match (← get).env.defEqCache[rootCacheKey]? with
          | some v => pure (some (v, false))
          | none =>
            if cheapMode then
              match (← get).env.defEqCheapCache[rootCacheKey]? with
              | some v => pure (some (v, true))
              | none => pure none
            else
              pure none
        if let some (cached, fromCheap) := cached? then
          if fromCheap then
            modify fun s => { s with env := { s.env with
              defEqCheapCache := s.env.defEqCheapCache.insert cacheKey cached
              defEqCache := if cached then
                  s.env.defEqCache.insert cacheKey true
                else s.env.defEqCache } }
          else
            modify fun s => { s with env := { s.env with
              defEqCache := s.env.defEqCache.insert cacheKey cached
              defEqCheapCache := if cheapMode then
                  s.env.defEqCheapCache.insert cacheKey cached
                else s.env.defEqCheapCache } }
          if cached then
            modify fun s => { s with
              equivManager := s.equivManager.addEquiv aKey bKey }
          return cached
  isDefEqAfterRootCacheMiss a b aKey bKey cacheKey cheapMode

/-- Charged recursive DefEq tail after every O(1) equivalence/cache exit
misses. This owns depth restoration and the final cache/manager updates. -/
def isDefEqAfterRootCacheMiss (a b : KExpr m) (aKey bKey : EqKey)
    (cacheKey : Address × Address × Address) (cheapMode : Bool) :
    RecM m Bool := do
  -- Charge fuel only after the O(1) exits.
  TcM.bumpStats (m := m) fun s => { s with deqMisses := s.deqMisses + 1 }
  TcM.tick (m := m)
  modify fun s => { s with
    defEqDepth := s.defEqDepth + 1
    defEqPeak := max s.defEqPeak (s.defEqDepth + 1) }
  if (← get).defEqDepth > maxDefEqDepth then
    modify fun s => { s with defEqDepth := s.defEqDepth - 1 }
    throw .maxRecDepth
  let result ←
    try
      let r ← isDefEqInner a b
      pure (Except.ok r)
    catch e =>
      pure (Except.error e)
  modify fun s => { s with defEqDepth := s.defEqDepth - 1 }
  let ok ← match result with
    | .ok r => pure r
    | .error e => throw e
  if ok then
    -- Cheap-mode `true` is monotone (cheap-equal ⇒ FULL-equal).
    modify fun s => { s with
      equivManager := s.equivManager.addEquiv aKey bKey }
  if cheapMode then
    modify fun s => { s with env := { s.env with
      defEqCheapCache := s.env.defEqCheapCache.insert cacheKey ok
      defEqCache := if ok then s.env.defEqCache.insert cacheKey true
        else s.env.defEqCache } }
  else
    modify fun s => { s with env := { s.env with
      defEqCache := s.env.defEqCache.insert cacheKey ok } }
  return ok

def isDefEqInner (a b : KExpr m) : RecM m Bool := do
  -- Tier 1: quick structural.
  if (← quickDefEq a b) then
    return true
  isDefEqInnerAfterQuick a b

/-- Remaining recursive DefEq tiers after the quick structural probe misses.
Keeping this as a production-owned seam lets verification compose the
constructor-exhaustive Tier-1 proof without duplicating or restating the
subsequent reducer. -/
def isDefEqInnerAfterQuick (a b : KExpr m) : RecM m Bool := do
  -- Tier 1b: eager Bool.true reduction.
  if (← isBoolTrue b) && (← boolTrueReductionAllowed a) then
    if (← whnfIsBoolTrue a) then
      return true
    isDefEqInnerAfterBoolTrue a b
  else
    isDefEqInnerAfterFirstBoolGuardMiss a b

/-- Symmetric eager-Boolean direction, reached only when the first
recognition/policy guard was unavailable. -/
def isDefEqInnerAfterFirstBoolGuardMiss (a b : KExpr m) : RecM m Bool := do
  if (← isBoolTrue a) && (← boolTrueReductionAllowed b) then
    if (← whnfIsBoolTrue b) then
      return true
  isDefEqInnerAfterBoolTrue a b

/-- Remaining recursive DefEq tiers after the two eager `Bool.true`
directions both fail to accept. -/
def isDefEqInnerAfterBoolTrue (a b : KExpr m) : RecM m Bool := do
  -- Tier 1c: string-literal expansion BEFORE any whnf.
  if hasStringLiteralPair a b then
    if (← tryStringLitExpansion a b) then
      return true
    if (← tryStringLitExpansion b a) then
      return true
  isDefEqInnerAfterStringExpansion a b

/-- Remaining recursive DefEq tiers after literal String expansion fails to
accept in either direction. -/
def isDefEqInnerAfterStringExpansion (a b : KExpr m) : RecM m Bool := do
  -- Tier 1d: cheap structural passes.
  let ca ← whnfCoreForDefEq a
  let cb ← whnfCoreForDefEq b
  if ca.addr == cb.addr then
    return true
  if (← quickDefEq ca cb) then
    return true
  isDefEqInnerAfterCorePass a b

/-- Remaining recursive DefEq tiers after the cheap structural-core pass
fails to accept. -/
def isDefEqInnerAfterCorePass (a b : KExpr m) : RecM m Bool := do
  let wa ← whnfNoDeltaForDefEq a
  let wb ← whnfNoDeltaForDefEq b
  if wa.addr == wb.addr then
    return true
  if (← quickDefEq wa wb) then
    return true
  isDefEqInnerAfterNoDeltaPass wa wb

/-- Remaining recursive DefEq tiers after the cheap no-delta pass fails to
accept.  Inputs are the already normalized pair. -/
def isDefEqInnerAfterNoDeltaPass (wa wb : KExpr m) : RecM m Bool := do
  -- Tier 3: proof irrelevance (before delta).
  if (← tryProofIrrel wa wb) then
    return true
  isDefEqInnerAfterProofIrrelevance wa wb

/-- One iteration of the bounded lazy-delta comparison.  Nat-offset
comparison is isolated at the front because its shared-offset injectivity
argument is distinct from the ordinary reduction branches. -/
def defEqLazyDeltaStep (state : KExpr m × KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let (wa, wb) := state
  if let some result ← tryDefEqOffset wa wb then
    return .done (.answer result)
  defEqLazyDeltaStepAfterOffsetMiss state

/-- Remaining lazy-delta iteration after the Nat-offset probe returns
`none`. -/
def defEqLazyDeltaStepAfterOffsetMiss (state : KExpr m × KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let (wa0, wb0) := state
  let mut wa := wa0
  let mut wb := wb0
  -- Nat primitives gated on closed terms (or eagerReduce).
  let natOk := (!wa.hasFVars && !wb.hasFVars) || (← get).eagerReduce
  if natOk then
    if let some wa2 ← tryReduceNat wa then
      return .done (.answer (← isDefEqCall wa2 wb))
    if let some wb2 ← tryReduceNat wb then
      return .done (.answer (← isDefEqCall wa wb2))
  defEqLazyDeltaStepAfterNatMiss wa wb

/-- Remaining lazy-delta iteration after the gated Nat reducers both miss or
are skipped. -/
def defEqLazyDeltaStepAfterNatMiss (wa0 wb0 : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  if let some wa2 ← tryReduceNative wa then
    return .done (.answer (← isDefEqCall wa2 wb))
  if let some wb2 ← tryReduceNative wb then
    return .done (.answer (← isDefEqCall wa wb2))
  if let some wa2 ← tryReduceDecidable wa then
    return .done (.answer (← isDefEqCall wa2 wb))
  if let some wb2 ← tryReduceDecidable wb then
    return .done (.answer (← isDefEqCall wa wb2))
  defEqLazyDeltaStepAfterAcceleratorMiss wa wb

/-- Remaining lazy-delta iteration after native and Decidable acceleration
both miss.  In the no-acceleration verification layer this is the exact tail
of `defEqLazyDeltaStepAfterNatMiss`. -/
def defEqLazyDeltaStepAfterAcceleratorMiss (wa0 wb0 : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  let aHead := headConstId wa
  let bHead := headConstId wb
  let aDelta ← classifyDeltaHead wa
  let bDelta ← classifyDeltaHead wb
  if !aDelta && !bDelta then
    return .done (.stopped wa wb)
  defEqLazyDeltaStepAfterDeltaClassification wa wb aHead bHead aDelta bDelta

/-- Remaining lazy-delta iteration after at least one head has been
classified as delta-reducible. -/
def defEqLazyDeltaStepAfterDeltaClassification (wa0 wb0 : KExpr m)
    (aHead bHead : Option (KId m)) (aDelta bDelta : Bool) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  -- Before unfolding, try reducing projection apps on the other side.
  if aDelta && !bDelta then
    if let some wb2 ← tryUnfoldProjApp wb then
      return .next (wa, wb2)
  else if bDelta && !aDelta then
    if let some wa2 ← tryUnfoldProjApp wa then
      return .next (wa2, wb)
  defEqLazyDeltaStepAfterProjectionMiss wa wb aHead bHead aDelta bDelta

/-- Remaining lazy-delta iteration after the asymmetric projection-app probe
is inapplicable or returns `none`. -/
def defEqLazyDeltaStepAfterProjectionMiss (wa0 wb0 : KExpr m)
    (aHead bHead : Option (KId m)) (aDelta bDelta : Bool) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  if aDelta && bDelta then
    let waW ← rankDeltaHead aHead
    let wbW ← rankDeltaHead bHead
    if waW == wbW then
      defEqLazyDeltaStepWithEqualRank wa wb aHead bHead
    else if compareRank waW wbW == .gt then
      defEqLazyDeltaStepWithLeftDelta wa wb
    else
      defEqLazyDeltaStepWithRightDelta wa wb
  else if aDelta then
    defEqLazyDeltaStepWithLeftDelta wa wb
  else
    defEqLazyDeltaStepWithRightDelta wa wb

/-- Run same-head spine comparison behind its narrow rejection-only cache.
A cache hit skips the attempt; a genuine miss records exactly the canonical
operand/context key. -/
def trySameHeadSpineCached (speculative : Bool) (left right : KExpr m) :
    RecM m (Option Bool) := do
  let failureKey := defEqFailureKey left right (← TcM.defEqCtxKey left right)
  if (← get).env.defEqFailure.contains failureKey then
    return none
  let attempt : RecM m (Option Bool) := if speculative then
    trySameHeadSpineSpeculative left right
  else
    trySameHeadSpine left right
  let result ← attempt
  match result with
  | some result => return some result
  | none =>
      modify fun state => { state with env := { state.env with
        defEqFailure := state.env.defEqFailure.insert failureKey } }
      return none

/-- Equal-rank lazy delta: Regular heads use the standard same-head path;
other hints use the fuel-bounded speculative path. Both retain the narrow
rejection cache before ordinary two-sided unfolding. -/
def defEqLazyDeltaStepWithEqualRank (wa0 wb0 : KExpr m)
    (aHead bHead : Option (KId m)) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  -- Same-head-spine attempt, guarded by the narrow negative cache.
  if let (some ah, some bh) := (aHead, bHead) then
    if ah.addr == bh.addr then
      let speculative := !(← isRegular ah)
      if let some result ← trySameHeadSpineCached speculative wa wb then
        return .done (.answer result)
  defEqLazyDeltaStepAfterSameHeadMiss wa wb

/-- Equal-rank continuation after the guarded same-head attempt is skipped,
cached as a failure, or returns `none`. -/
def defEqLazyDeltaStepAfterSameHeadMiss (wa0 wb0 : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  let mut wa := wa0
  let mut wb := wb0
  -- Equal rank: unfold BOTH sides.
  let ua ← deltaUnfoldOne wa
  let ub ← deltaUnfoldOne wb
  match ua, ub with
  | some ua, some ub =>
    wa ← whnfNoDeltaForDefEq ua
    wb ← whnfNoDeltaForDefEq ub
  | some ua, none =>
    wa ← whnfNoDeltaForDefEq ua
  | none, some ub =>
    wb ← whnfNoDeltaForDefEq ub
  | none, none =>
    return .done (.stopped wa wb)
  finishDefEqLazyDeltaStep wa wb

/-- Unfold and no-delta-normalize only the left operand, then perform the
common finishing checks. -/
def defEqLazyDeltaStepWithLeftDelta (wa wb : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  match (← deltaUnfoldOne wa) with
  | some unfolded =>
      let reduced ← whnfNoDeltaForDefEq unfolded
      finishDefEqLazyDeltaStep reduced wb
  | none =>
      return .done (.stopped wa wb)

/-- Symmetric one-sided delta unfold for the right operand. -/
def defEqLazyDeltaStepWithRightDelta (wa wb : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  match (← deltaUnfoldOne wb) with
  | some unfolded =>
      let reduced ← whnfNoDeltaForDefEq unfolded
      finishDefEqLazyDeltaStep wa reduced
  | none =>
      return .done (.stopped wa wb)

/-- Finish one productive lazy-delta iteration with the two cheap equality
checks, otherwise expose the transformed pair to the bounded driver. -/
def finishDefEqLazyDeltaStep (wa wb : KExpr m) :
    RecM m (BoundedStep (KExpr m × KExpr m) (LazyDeltaLoopResult m)) := do
  if wa.addr == wb.addr then
    return .done (.answer true)
  if (← quickDefEq wa wb) then
    return .done (.answer true)
  return .next (wa, wb)

/-- Run the iterative lazy-delta comparison with the kernel's WHNF fuel
bound. -/
def runDefEqLazyDelta (wa wb : KExpr m) :
    RecM m (LazyDeltaLoopResult m) :=
  runBounded defEqLazyDeltaStep maxWhnfFuel.toNat (wa, wb)

/-- Continue the recursive comparison after lazy delta can no longer make
progress. -/
def isDefEqAfterLazyDeltaStopped (wa wb : KExpr m) : RecM m Bool := do
  -- Tier 4b: post-delta structural congruence.
  if (← tryStructuralCongruence wa wb) then
    return true
  -- Tier 4c: second structural pass — whnfCore, NOT full whnf.
  let waCore ← whnfCore wa
  let wbCore ← whnfCore wb
  let waChanged := waCore.addr != wa.addr
  let wbChanged := wbCore.addr != wb.addr
  if waChanged || wbChanged then
    return (← isDefEqCall waCore wbCore)
  if waCore.addr == wbCore.addr then
    return true
  if (← quickDefEq waCore wbCore) then
    return true
  -- Tier 4d: app-spine comparison.
  if (← tryDefEqApp waCore wbCore) then
    return true
  isDefEqWhnf waCore wbCore

/-- Remaining recursive DefEq tiers after the pre-delta proof-irrelevance
attempt fails to accept. -/
def isDefEqInnerAfterProofIrrelevance
    (wa wb : KExpr m) : RecM m Bool := do
  match ← runDefEqLazyDelta wa wb with
  | .answer result => return result
  | .stopped wa wb => isDefEqAfterLazyDeltaStopped wa wb

/-- Tier-1 quick structural: same ctor, same children (binders open both
    bodies with the SAME fresh fvar — the common-fvar trick). -/
def quickDefEq (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .sort u1 _, .sort u2 _ => return univEq u1 u2
  | .lam name bi ty1 body1 _, .lam _ _ ty2 body2 _ =>
    quickBinder name bi ty1 body1 ty2 body2
  | .all name bi ty1 body1 _, .all _ _ ty2 body2 _ =>
    quickBinder name bi ty1 body1 ty2 body2
  | _, _ => return false

def quickBinder (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty1 body1 ty2 body2 : KExpr m) : RecM m Bool := do
  if !(← isDefEqCall ty1 ty2) then
    return false
  withLctxScope do
    let (b1Open, fvId) ← TcM.openBinder name bi ty1 body1
    let fv ← TcM.intern (KExpr.mkFVar fvId name)
    let b2Open ← TcM.runIntern (instantiateRev body2 #[fv])
    isDefEqCall b1Open b2Open

/-- List recursion underlying application-spine argument comparison. -/
def allDefEqSpineArgsList : List (KExpr m × KExpr m) → RecM m Bool
  | [] => pure true
  | (left, right) :: rest => do
      if !(← isDefEqCall left right) then
        return false
      allDefEqSpineArgsList rest

/-- Compare a finite array of expression pairs through the recursive DefEq
callback, stopping at the first rejection.  Both same-head and general
application-spine comparison use this exact left-to-right loop. -/
def allDefEqSpineArgs (pairs : Array (KExpr m × KExpr m)) : RecM m Bool :=
  allDefEqSpineArgsList pairs.toList

/-- Pure recursive comparison of universe pairs used by constant-headed
spine checks. -/
def allDefEqUniversesList : List (KUniv m × KUniv m) → Bool
  | [] => true
  | (left, right) :: rest =>
      univEq left right && allDefEqUniversesList rest

/-- Exact constant-instance gate: equal arity and pairwise universe
equality in production order. -/
def sameDefEqUniverses (left right : Array (KUniv m)) : Bool :=
  left.size == right.size &&
    allDefEqUniversesList (left.zip right).toList

/-- Both are `C us args` with the same head: compare spines without
    unfolding. `none` means "not applicable / spine differs". -/
def trySameHeadSpine (a b : KExpr m) : RecM m (Option Bool) := do
  let (aHead, aArgs) := a.collectSpine
  let (bHead, bArgs) := b.collectSpine
  let .const aId aUs _ := aHead | return none
  let .const bId bUs _ := bHead | return none
  if aId.addr != bId.addr || aArgs.size != bArgs.size then
    return none
  if !sameDefEqUniverses aUs bUs then
    return none
  if !(← allDefEqSpineArgs (aArgs.zip bArgs)) then
    return none
  return some true

/-- Run a non-Regular same-head comparison with bounded local recursive fuel.
Nested speculative attempts inherit the remaining slice. Fuel/depth exhaustion
means only that speculation missed; consumed fuel is charged to the enclosing
constant check before ordinary delta reduction resumes. -/
def trySameHeadSpineSpeculative (a b : KExpr m) :
    RecM m (Option Bool) := do
  let saved ← get
  let savedFuel := saved.recFuel
  let nested := savedFuel <= sameHeadSpeculationAttemptFuel
  if !nested && saved.fuelBudget - savedFuel >= sameHeadSpeculationStartFuel then
    return none
  let localFuel := min savedFuel sameHeadSpeculationAttemptFuel
  modify fun s => { s with recFuel := localFuel }
  let result : Except (TcError m) (Option Bool) ←
    try
      let answer ← trySameHeadSpine a b
      pure (.ok answer)
    catch e =>
      pure (.error e)
  let consumed := localFuel - (← get).recFuel
  modify fun s => { s with
    recFuel := savedFuel - min savedFuel consumed }
  match result with
  | .ok answer => return answer
  | .error .maxRecDepth | .error .maxRecFuel => return none
  | .error e => throw e

/-- Short-circuiting application branch of the final structural comparison. -/
def tryDefEqWhnfApp (f1 a1 f2 a2 : KExpr m) :
    RecM m (Option Bool) := do
  -- MUST short-circuit (Rust `&&` does; Lean's `(← _) && (← _)` runs
  -- BOTH actions). For dependent apps the second component is often a
  -- PROOF: comparing proof pairs whose value pair already failed forces
  -- unbounded proof normalization.
  if (← isDefEqCall f1 f2) then
    if (← isDefEqCall a1 a2) then
      return some true
  return none

/-- Let-declaration branch of the final structural comparison. -/
def tryDefEqWhnfLet (name : m.F Name)
    (ty1 v1 body1 ty2 v2 body2 : KExpr m) :
    RecM m (Option Bool) := do
  -- Normally zeta-reduced before reaching here; push LDecl in case.
  if (← isDefEqCall ty1 ty2) then
    if (← isDefEqCall v1 v2) then
      let r ← withLctxScope do
        let (b1Open, fv, _) ← TcM.openLetWithFV name ty1 v1 body1
        let b2Open ← TcM.runIntern (instantiateRev body2 #[fv])
        isDefEqCall b1Open b2Open
      if r then
        return some true
  return none

/-- Constructor-directed prefix of the final WHNF comparison.  `some answer`
is a terminal verdict; `none` means that production must continue with the
Nat/eta/String/structural fallbacks. -/
def tryDefEqWhnfStructural (a b : KExpr m) : RecM m (Option Bool) := do
  match a, b with
  | .sort u1 _, .sort u2 _ => return some (univEq u1 u2)
  | .var i _ _, .var j _ _ =>
    if i == j then
      return some true
  | .const id1 us1 _, .const id2 us2 _ =>
    if id1.addr == id2.addr && sameDefEqUniverses us1 us2 then
      return some true
  | .app f1 a1 _, .app f2 a2 _ =>
    return (← tryDefEqWhnfApp f1 a1 f2 a2)
  | .lam name bi ty1 body1 _, .lam _ _ ty2 body2 _ =>
    if (← quickBinder name bi ty1 body1 ty2 body2) then
      return some true
  | .all name bi ty1 body1 _, .all _ _ ty2 body2 _ =>
    if (← quickBinder name bi ty1 body1 ty2 body2) then
      return some true
  | .letE name ty1 v1 body1 _ _, .letE _ ty2 v2 body2 _ _ =>
    return (← tryDefEqWhnfLet name ty1 v1 body1 ty2 v2 body2)
  | .nat v1 _ _, .nat v2 _ _ => return some (v1 == v2)
  | .str v1 _ _, .str v2 _ _ => return some (v1 == v2)
  | _, _ => pure ()
  return none

/-- Optional Nat literal/constructor bridge at the head of the final-WHNF
fallback chain. -/
def tryDefEqWhnfNat (a b : KExpr m) : RecM m (Option Bool) := do
  if (← isNatLike a) && (← isNatLike b) then
    return some (← isDefEqNat a b)
  return none

/-- Ordered bidirectional eta attempts after the outer syntax guard accepts. -/
def tryDefEqWhnfEtaAfterGuard (a b : KExpr m) : RecM m (Option Bool) := do
  if (← tryEtaExpansion a b) then
    return some true
  if (← tryEtaExpansion b a) then
    return some true
  return none

/-- Optional lambda-eta phase in the final-WHNF fallback chain.  The two
directions retain production's ordering and short-circuit behavior. -/
def tryDefEqWhnfEta (a b : KExpr m) : RecM m (Option Bool) := do
  let aIsLam := match a with | .lam .. => true | _ => false
  let bIsLam := match b with | .lam .. => true | _ => false
  if aIsLam || bIsLam then
    tryDefEqWhnfEtaAfterGuard a b
  else
    return none

/-- Ordered bidirectional String-literal expansion attempts after the outer
syntax guard accepts. -/
def tryDefEqWhnfStringAfterGuard (a b : KExpr m) :
    RecM m (Option Bool) := do
  if (← tryStringLitExpansion a b) then
    return some true
  if (← tryStringLitExpansion b a) then
    return some true
  return none

/-- Optional String-literal expansion phase in the final-WHNF fallback
chain. -/
def tryDefEqWhnfString (a b : KExpr m) : RecM m (Option Bool) := do
  if hasStringLiteralPair a b then
    tryDefEqWhnfStringAfterGuard a b
  else
    return none

/-- Ordered bidirectional structure-eta attempts. -/
def tryDefEqWhnfStructEta (a b : KExpr m) : RecM m (Option Bool) := do
  if (← tryEtaStruct a b) then
    return some true
  if (← tryEtaStruct b a) then
    return some true
  return none

/-- Final proof-irrelevance fallback after the unit-like probe misses. -/
def isDefEqWhnfAfterUnit (a b : KExpr m) : RecM m Bool :=
  tryProofIrrel a b

/-- Remaining final-WHNF fallbacks after structure eta misses. -/
def isDefEqWhnfAfterStructEta (a b : KExpr m) : RecM m Bool := do
  if (← tryDefEqUnit a b) then
    return true
  isDefEqWhnfAfterUnit a b

/-- Remaining final-WHNF fallbacks after String expansion misses. -/
def isDefEqWhnfAfterString (a b : KExpr m) : RecM m Bool := do
  match (← tryDefEqWhnfStructEta a b) with
  | some answer => return answer
  | none => isDefEqWhnfAfterStructEta a b

/-- Remaining final-WHNF fallbacks after lambda eta misses. -/
def isDefEqWhnfAfterEta (a b : KExpr m) : RecM m Bool := do
  match (← tryDefEqWhnfString a b) with
  | some answer => return answer
  | none => isDefEqWhnfAfterString a b

/-- Remaining final-WHNF fallbacks after the Nat bridge misses. -/
def isDefEqWhnfAfterNat (a b : KExpr m) : RecM m Bool := do
  match (← tryDefEqWhnfEta a b) with
  | some answer => return answer
  | none => isDefEqWhnfAfterEta a b

/-- Remaining final-WHNF fallbacks after the constructor-directed prefix has
no terminal result. -/
def isDefEqWhnfAfterStructural (a b : KExpr m) : RecM m Bool := do
  match (← tryDefEqWhnfNat a b) with
  | some answer => return answer
  | none => isDefEqWhnfAfterNat a b

/-- Tier 5: full structural + eta / struct-eta / unit / proof irrelevance. -/
def isDefEqWhnf (a b : KExpr m) : RecM m Bool := do
  match (← tryDefEqWhnfStructural a b) with
  | some answer => return answer
  | none => isDefEqWhnfAfterStructural a b

/-- Proof irrelevance: both proofs of the same Prop. -/
def tryProofIrrel (a b : KExpr m) : RecM m Bool := do
  let some aTy ← try? (inferOnlyCall a) | return false
  if !(← isPropType aTy) then
    return false
  let some bTy ← try? (inferOnlyCall b) | return false
  isDefEqCall aTy bTy

/-- Uncached proposition classification.  Inner-chain errors and inferred
types that do not normalize to a sort are conservative negative results. -/
def classifyPropTypeUncached (ty : KExpr m) : RecM m Bool := do
  match (← try? (inferOnlyCall ty)) with
    | none => pure false
    | some sort =>
      match (← try? (whnf sort)) with
      | some (.sort u _) => pure u.isSemanticZero
      | _ => pure false

/-- Is `ty : Sort 0`? Memoized on `(tyAddr, ctxAddr)`; inner-chain errors
    treated as non-prop. -/
def isPropType (ty : KExpr m) : RecM m Bool := do
  let cacheKey := (ty.addr, ← TcM.ctxAddrForLbr (m := m) ty.lbr)
  if let some cached := (← get).env.isPropCache[cacheKey]? then
    return cached
  let result ← classifyPropTypeUncached ty
  modify fun s => { s with env := { s.env with
    isPropCache := s.env.isPropCache.insert cacheKey result } }
  return result

/-- Classify one inductive declaration as unit-like: zero indices, exactly
one constructor, and no constructor fields. -/
def isUnitLikeInductive (indId : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst indId) with
    | some (.indc (indices := indices) (ctors := ctors) ..) =>
      if indices != 0 || ctors.size != 1 then
        return false
      else
        match (← TcM.tryGetConst ctors[0]!) with
        | some (.ctor (fields := fields) ..) => return fields == 0
        | _ => return false
    | _ => return false

/-- Unit-like (non-recursive, 0 indices, 1 nullary ctor): any two
    inhabitants of the same unit-like type are def-eq. -/
def tryDefEqUnit (a b : KExpr m) : RecM m Bool := do
  let some aTy ← try? (inferOnlyCall a) | return false
  let some aTyW ← try? (whnf aTy) | return false
  let (aHead, _) := aTyW.collectSpine
  let .const aInd _ _ := aHead | return false
  if !(← isUnitLikeInductive aInd) then
    return false
  let some bTy ← try? (inferOnlyCall b) | return false
  isDefEqCall aTyW bTy

/-- Nat-like comparison after the direct literal/literal case misses. -/
def isDefEqNatAfterLiteral (a b : KExpr m) : RecM m Bool := do
  if (← isNatZero a) && (← isNatZero b) then
    return true
  match (← natSuccOf a), (← natSuccOf b) with
  | some aPred, some bPred => isDefEqCall aPred bPred
  | _, _ => return false

/-- Nat-like comparison: literal fast path, zero/succ peeling. -/
def isDefEqNat (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .nat va _ _, .nat vb _ _ => return va == vb
  | _, _ => isDefEqNatAfterLiteral a b

/-- Nat offset comparison in the lazy delta loop (`isDefEqOffset`),
    generalized to offset form: each side decomposes to `base + offset`
    (`Lit n`, `succ` layers, and the compact stuck `Nat.add base (Lit m)`
    form WHNF leaves — all read in O(1) per layer), the shared offset is
    stripped in ONE step, and the remainders compare through full def-eq.
    This collapses `succ^k(x) ≟ succ^k(x)` from k def-eq recursion levels
    (which blew the def-eq depth limit for large k) to one. Stripping is
    verdict-preserving: `+k` is definitionally injective, the same
    semantics a one-succ peel relies on. Non-offset shapes fall back
    (`none`) to the generic path. Mirrors def_eq.rs `try_def_eq_offset`. -/
def tryDefEqOffset (a b : KExpr m) : RecM m (Option Bool) := do
  match a, b with
  | .nat va _ _, .nat vb _ _ => return some (va == vb)
  | _, _ => pure ()
  tryDefEqOffsetAfterLiteral a b

/-- Remaining Nat-offset comparison after the direct literal/literal case
does not apply. -/
def tryDefEqOffsetAfterLiteral (a b : KExpr m) :
    RecM m (Option Bool) := do
  if (← isNatZero a) && (← isNatZero b) then
    return some true
  tryDefEqOffsetAfterZeroMiss a b

/-- Remaining generalized offset path after neither the direct literal pair
nor the joint Nat-zero probe accepts. -/
def tryDefEqOffsetAfterZeroMiss (a b : KExpr m) :
    RecM m (Option Bool) := do
  -- Quick reject: decompose walks app spines, so only run it when both
  -- heads are plausibly offset-shaped (a one-succ peel rejects non-Nat
  -- shapes in O(1) off the head — keep that property).
  let p ← prims
  if !natOffsetCandidate p a || !natOffsetCandidate p b then
    return none
  tryDefEqOffsetAfterCandidates a b

/-- Remaining offset decomposition and rebuild after both allocation-free
candidate guards accept. -/
def tryDefEqOffsetAfterCandidates (a b : KExpr m) :
    RecM m (Option Bool) := do
  let some (baseA, ka) ← natOffsetDecompose a | return none
  let some (baseB, kb) ← natOffsetDecompose b | return none
  let k := min ka kb
  if k == 0 then
    -- No shared offset to strip (e.g. literal 0 vs offset-shaped): defer
    -- to the generic path.
    return none
  let ra ← natOffsetRebuild baseA (ka - k)
  let rb ← natOffsetRebuild baseB (kb - k)
  return some (← isDefEqCall ra rb)

/-- Expand a string literal to ctor form and compare. -/
def tryStringLitExpansion (t s : KExpr m) : RecM m Bool := do
  let .str strVal _ _ := t | return false
  let expanded ← strLitToConstructor strVal
  isDefEqCall expanded s

/-- Build and compare the concrete lambda used by eta after inference has
exposed the non-lambda operand's function domain. -/
def compareEtaExpansion (t s : KExpr m) (name : m.F Name)
    (bi : m.F Lean.BinderInfo) (ty : KExpr m) : RecM m Bool := do
  let sLifted ← TcM.runIntern (lift s 1 0)
  let v0 ← TcM.intern (.mkVar 0 anonN : KExpr m)
  let body ← TcM.intern (KExpr.mkApp sLifted v0)
  let sLam ← TcM.intern (.mkLam name bi ty body)
  isDefEqCall t sLam

/-- Lambda-eta construction after the syntactic lambda/non-lambda guard has
accepted. -/
def tryEtaExpansionAfterGuard (t s : KExpr m) : RecM m Bool := do
  let some sTy ← try? (inferOnlyCall s) | return false
  let some sTyWhnf ← try? (whnf sTy) | return false
  let .all name bi ty _ _ := sTyWhnf | return false
  compareEtaExpansion t s name bi ty

/-- Lambda eta: `t` a lambda, `s` not — wrap `s` as `λ(ty). s #0`. -/
def tryEtaExpansion (t s : KExpr m) : RecM m Bool := do
  let tIsLam := match t with | .lam .. => true | _ => false
  let sIsLam := match s with | .lam .. => true | _ => false
  if !tIsLam || sIsLam then
    return false
  tryEtaExpansionAfterGuard t s

/-- Struct eta: `s` a fully-applied ctor of a struct-like type; compare
    `prj i t ≡ s.args[params+i]` per field (types def-eq first; no Prop
    guard here — equality checking, not term construction). -/
def tryEtaStruct (t s : KExpr m) : RecM m Bool := do
  let tNorm ← normalizeEtaStructSource t
  tryEtaStructAfterNormalization tNorm s

/-- Caught no-delta normalization used by structure eta.  A reducer error
retains the original source exactly, matching production's non-backtracking
fallback. -/
def normalizeEtaStructSource (t : KExpr m) : RecM m (KExpr m) := do
  match (← try? (whnfNoDelta t)) with
  | some w => pure w
  | none => pure t

/-- Constructor-head lookup and metadata selection after the left operand
has been normalized for structure eta. -/
def tryEtaStructAfterNormalization (tNorm s : KExpr m) : RecM m Bool := do
  let (sHead, sArgs) := s.collectSpine
  let .const ctorId _ _ := sHead | return false
  let (inductId, numParams, numFields) ← match (← TcM.tryGetConst ctorId) with
    | some (.ctor (induct := induct) (params := params) (fields := fields) ..) =>
      pure (induct, params.toNat, fields.toNat)
    | _ => return false
  tryEtaStructAfterConstructor inductId numParams numFields tNorm s sArgs

/-- Size, classifier, inference, and field-comparison tail for the exact
constructor metadata selected by `tryEtaStructAfterNormalization`. -/
def tryEtaStructAfterConstructor (inductId : KId m)
    (numParams numFields : Nat) (tNorm s : KExpr m)
    (sArgs : Array (KExpr m)) : RecM m Bool := do
  if sArgs.size != numParams + numFields then
    return false
  if !(← isStructLike inductId) then
    return false
  let some sTy ← try? (inferOnlyCall s) | return false
  let some tTy ← try? (inferOnlyCall tNorm) | return false
  if !(← isDefEqCall tTy sTy) then
    return false
  tryEtaStructAfterTypes inductId numParams numFields tNorm sArgs

/-- Structure-eta tail after both operands have been shown to have
definitionally equal types.  The common-base shortcut precedes the explicit
field loop exactly as in the original implementation. -/
def tryEtaStructAfterTypes (inductId : KId m) (numParams numFields : Nat)
    (tNorm : KExpr m) (sArgs : Array (KExpr m)) : RecM m Bool := do
  if let some base ← etaExpansionBase inductId numParams numFields sArgs then
    if (← isDefEqCall tNorm base) then
      return true
  tryEtaStructFields inductId numParams tNorm sArgs numFields 0

/-- Left-to-right structure-eta field comparison.  `fuel` is the number of
remaining fields and `field` is the concrete projection index; naming this
loop exposes its exact generated projections and short-circuit behavior. -/
def tryEtaStructFields (inductId : KId m) (numParams : Nat)
    (tNorm : KExpr m) (sArgs : Array (KExpr m)) :
    Nat → Nat → RecM m Bool
  | 0, _ => pure true
  | fuel + 1, field => do
      let proj ← TcM.intern (.mkPrj inductId field.toUInt64 tNorm)
      if !(← isDefEqCall proj sArgs[numParams + field]!) then
        return false
      tryEtaStructFields inductId numParams tNorm sArgs fuel (field + 1)

/-- If every ctor field is `prj i base` of one common base, return it. -/
def etaExpansionBase (inductId : KId m) (numParams numFields : Nat)
    (args : Array (KExpr m)) : RecM m (Option (KExpr m)) := do
  etaExpansionBaseLoop inductId numParams args numFields 0 none

/-- Left-to-right common-base scan used by the structure-eta shortcut.  The
explicit accumulator and remaining-field count retain the original WHNF and
caught-error order while making partial exits available to verification. -/
def etaExpansionBaseLoop (inductId : KId m) (numParams : Nat)
    (args : Array (KExpr m)) :
    Nat → Nat → Option (KExpr m) → RecM m (Option (KExpr m))
  | 0, _, base => pure base
  | fuel + 1, fieldIdx, base => do
      let field := args[numParams + fieldIdx]!
      let field ← whnfNoDelta field
      let .prj id idx val _ := field | return none
      if id.addr != inductId.addr || idx.toNat != fieldIdx then
        return none
      etaExpansionBaseAfterProjection inductId numParams args fuel
        fieldIdx base val

/-- Caught optional normalization of one projection base in the common-base
scan. -/
def etaExpansionBaseAfterProjection (inductId : KId m) (numParams : Nat)
    (args : Array (KExpr m)) (fuel fieldIdx : Nat)
    (base : Option (KExpr m)) (value : KExpr m) :
    RecM m (Option (KExpr m)) := do
  match (← try? (whnfNoDelta value)) with
  | some normalized =>
      etaExpansionBaseAfterValue inductId numParams args fuel fieldIdx base
        normalized
  | none =>
      etaExpansionBaseAfterValue inductId numParams args fuel fieldIdx base
        value

/-- Accumulator check after one projection base has been selected. -/
def etaExpansionBaseAfterValue (inductId : KId m) (numParams : Nat)
    (args : Array (KExpr m)) (fuel fieldIdx : Nat)
    (base : Option (KExpr m)) (value : KExpr m) :
    RecM m (Option (KExpr m)) :=
  match base with
  | some prior => do
      if prior.addr != value.addr then
        return none
      etaExpansionBaseLoop inductId numParams args fuel
        (fieldIdx + 1) base
  | none =>
      etaExpansionBaseLoop inductId numParams args fuel
        (fieldIdx + 1) (some value)

/-- App-spine comparison (isDefEqApp). -/
def tryDefEqApp (a b : KExpr m) : RecM m Bool := do
  let aIsApp := match a with | .app .. => true | _ => false
  let bIsApp := match b with | .app .. => true | _ => false
  if !aIsApp || !bIsApp then
    return false
  let (aHead, aArgs) := a.collectSpine
  let (bHead, bArgs) := b.collectSpine
  if aArgs.size != bArgs.size then
    return false
  if !(← isDefEqCall aHead bHead) then
    return false
  allDefEqSpineArgs (aArgs.zip bArgs)

/-- Post-delta structural congruence (Const/Var/Prj). -/
def tryStructuralCongruence (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .const id1 us1 _, .const id2 us2 _ =>
    return id1.addr == id2.addr && sameDefEqUniverses us1 us2
  | .var i _ _, .var j _ _ => return i == j
  | .prj id1 f1 v1 _, .prj id2 f2 v2 _ =>
    if id1.addr != id2.addr || f1 != f2 then
      return false
    lazyDeltaProjReduction id1 f1 v1 v2
  | _, _ => return false

def lazyDeltaProjReduction (structId : KId m) (field : UInt64)
    (a0 b0 : KExpr m) : RecM m Bool := do
  let step (state : KExpr m × KExpr m) :
      RecM m (BoundedStep (KExpr m × KExpr m) Bool) := do
    let (a, b) := state
    let (outcome, a, b) ← lazyDeltaReductionStep a b
    match outcome with
    | .equal => return .done true
    | .continue' => return .next (a, b)
    | .unknown =>
      let pa ← tryProjReduce structId field a
      let pb ← tryProjReduce structId field b
      match pa, pb with
      | some pa, some pb => return .done (← isDefEqCall pa pb)
      | _, _ => return .done (← isDefEqCall a b)
  runBounded step maxWhnfFuel.toNat (a0, b0)

def lazyDeltaReductionStep (a0 b0 : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let aHead := headConstId a0
  let bHead := headConstId b0
  let aDelta ← classifyDeltaHead a0
  let bDelta ← classifyDeltaHead b0
  lazyDeltaReductionStepAfterClassification a0 b0 aHead bHead aDelta bDelta

/-- Remaining projection-directed delta step after both head-classification
lookups.  Naming this tail exposes lazy-ingress preservation independently
from the reduction/rank branches without changing their execution order. -/
def lazyDeltaReductionStepAfterClassification (a0 b0 : KExpr m)
    (aHead bHead : Option (KId m)) (aDelta bDelta : Bool) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let mut a := a0
  let mut b := b0
  if !aDelta && !bDelta then
    return (.unknown, a, b)
  lazyDeltaReductionStepAfterActive a b aHead bHead aDelta bDelta

/-- Active projection-directed delta branches after at least one operand has
been classified as reducible. -/
def lazyDeltaReductionStepAfterActive (a0 b0 : KExpr m)
    (aHead bHead : Option (KId m)) (aDelta bDelta : Bool) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  if aDelta && !bDelta then
    match (← tryUnfoldProjApp b0) with
    | some b2 => finishLazyDeltaReductionStep a0 b2
    | none => lazyDeltaReductionStepWithLeftDelta a0 b0
  else if !aDelta && bDelta then
    match (← tryUnfoldProjApp a0) with
    | some a2 => finishLazyDeltaReductionStep a2 b0
    | none => lazyDeltaReductionStepWithRightDelta a0 b0
  else
    lazyDeltaReductionStepWithBothDelta a0 b0 aHead bHead

/-- Unfold and structural-normalize the left operand in the compact
projection-directed delta step. -/
def lazyDeltaReductionStepWithLeftDelta (a b : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  match (← deltaUnfoldOne a) with
  | some unfolded =>
      let reduced ← whnfCore unfolded
      finishLazyDeltaReductionStep reduced b
  | none => return (.unknown, a, b)

/-- Symmetric right-only branch of the compact projection-directed step. -/
def lazyDeltaReductionStepWithRightDelta (a b : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  match (← deltaUnfoldOne b) with
  | some unfolded =>
      let reduced ← whnfCore unfolded
      finishLazyDeltaReductionStep a reduced
  | none => return (.unknown, a, b)

/-- Rank dispatch when the projection-directed step classified both heads as
delta-reducible. -/
def lazyDeltaReductionStepWithBothDelta (a b : KExpr m)
    (aHead bHead : Option (KId m)) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let aId := aHead.get!
  let bId := bHead.get!
  let cmp := compareRank (← defRankId aId) (← defRankId bId)
  if cmp == .gt then
    lazyDeltaReductionStepWithLeftDelta a b
  else if cmp == .lt then
    lazyDeltaReductionStepWithRightDelta a b
  else
    lazyDeltaReductionStepWithEqualRank a b aId bId

/-- Equal-rank branch: try same-head congruence, then unfold both operands
and structural-normalize every successful result. -/
def lazyDeltaReductionStepWithEqualRank (a0 b0 : KExpr m)
    (aId bId : KId m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let mut a := a0
  let mut b := b0
  if aId.addr == bId.addr then
    let result ← if (← isRegular aId) then
        trySameHeadSpine a b
      else
        trySameHeadSpineSpeculative a b
    if let some true := result then
      return (.equal, a, b)
  lazyDeltaReductionStepAfterSameHeadMiss a b

/-- Two-sided unfold/structural-normalization tail after the compact
same-head attempt does not prove equality. -/
def lazyDeltaReductionStepAfterSameHeadMiss (a0 b0 : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let mut a := a0
  let mut b := b0
  let a2 ← deltaUnfoldOne a
  let b2 ← deltaUnfoldOne b
  match a2, b2 with
  | some a2, some b2 =>
    a ← whnfCore a2
    b ← whnfCore b2
  | some a2, none =>
    a ← whnfCore a2
  | none, some b2 =>
    b ← whnfCore b2
  | none, none => return (.unknown, a, b)
  finishLazyDeltaReductionStep a b

/-- Common address/quick-structural finish for a productive compact delta
step. -/
def finishLazyDeltaReductionStep (a b : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  if a.addr == b.addr || (← quickDefEq a b) then
    return (.equal, a, b)
  return (.continue', a, b)

/-- Head-Prj: one whnf-no-delta attempt (tryUnfoldProjApp). -/
def tryUnfoldProjApp (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, _) := e.collectSpine
  match head with
  | .prj .. => pure ()
  | _ => return none
  let reduced ← whnfNoDelta e
  if reduced.addr == e.addr then
    return none
  return some reduced

end

end RecM

end Ix.Tc

end
end
