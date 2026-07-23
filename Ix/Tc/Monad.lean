module

public import Ix.Tc.Env
public import Ix.Tc.Equiv
public import Ix.Tc.Primitive
public import Ix.Tc.Subst
public import Ix.Tc.Lctx

/-!
Mirror: crates/kernel/src/tc.rs

The type-checking monad and core helpers. Rust's `TypeChecker<'a, M>` borrows
a worker-owned `KEnv`; here the two fuse into one `TcState m` threaded by
`TcM m := EStateM (TcError m) (TcState m)`.

**`EStateM`, not `StateT _ (Except _)`** — load-bearing: Rust
catches-and-continues while holding `&mut KEnv` (e.g. `synth_ctor_when_k`
swallows errors, `check_recursor_member` discards generation failures), and
pre-error state mutations (cache inserts, consumed `recFuel`) survive.
`EStateM`'s non-backtracking `tryCatch` matches; `StateT`-over-`Except` would
silently reset fuel and caches on caught errors and diverge from Rust.
Swallowed-error frame leaks (ctx frames pushed before a caught throw) are
intentional Rust parity.

Fuels are data-level and placed exactly where Rust places them
(post-cache-miss). The `IX_MAX_REC_FUEL` env override is not ported.

Cross-file recursion (whnf ↔ infer ↔ def_eq) is tied through a `Methods m`
record + `RecM m := ReaderT (Methods m) (TcM m)`; the knot is tied by one
`partial def` in `Ix.Tc.Knot`. Only back-edges go through the record.

Not ported (diagnostics/profiling only): perf counters, hot-miss sampler,
`def_eq_trace_depth`, profile sink, `debug_label` env filters.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap HashSet)

/-- Content-addressed context identity for the empty context. -/
def emptyCtxAddr : Address :=
  Address.blake3 "ix.kernel.ctx.empty".toUTF8

/-- Maximum iterations in the WHNF delta loop (local per-call). -/
def maxWhnfFuel : UInt32 := 10_000

/-- Maximum recursion depth for `isDefEq`. -/
def maxDefEqDepth : UInt32 := 2_000

/-- Shared recursive fuel budget. Ticked at exactly two sites: the `whnf`
    cache-miss path (Whnf.lean) and the `isDefEq` entry (DefEq.lean) —
    `infer`/`whnfCore` never tick, so fuel-exhaustion arguments need a
    lexicographic (fuel, term-size) measure, not "every hop ticks".
    See tc.rs for the sizing rationale
    (BVDecide-scale proofs legitimately exceed a million recursive
    steps). -/
def maxRecFuel : UInt64 := 10_000_000

/-- Per-check type-checker state fused with the kernel environment. -/
structure TcState (m : Mode) where
  /-- Kernel environment (constants, caches, intern table). -/
  env : KEnv m
  /-- Primitive constant KIds (resolved once at construction; Rust copies
      `env.prims()` onto the `TypeChecker`). -/
  prims : Primitives m
  /-- Local variable types, indexed by de Bruijn level. -/
  ctx : Array (KExpr m) := #[]
  /-- Let-bound values, parallel to `ctx` (`some val` for let frames). -/
  letVals : Array (Option (KExpr m)) := #[]
  /-- Number of active let-bindings in `ctx`. -/
  numLetBindings : Nat := 0
  /-- Content-addressed context identity, derived from the binding chain. -/
  ctxId : Address := emptyCtxAddr
  /-- Stack of previous ctx ids for O(1) pop. -/
  ctxIdStack : Array Address := #[]
  /-- Union-find for transitive def-eq caching (per-check). -/
  equivManager : EquivManager := {}
  /-- When true, `infer` skips def-eq checks (arg/let-value validation). -/
  inferOnly : Bool := false
  /-- Re-entrancy guard for native reduction. -/
  inNativeReduce : Bool := false
  /-- Incremented inside def-eq's cheap projection reductions; routes cheap
      results into the cheap-only caches. -/
  cheapRecursionDepth : UInt32 := 0
  /-- When true, the Bool.true fast path in isDefEq fires even on open terms. -/
  eagerReduce : Bool := false
  /-- Current def-eq recursion depth. -/
  defEqDepth : UInt32 := 0
  /-- Peak def-eq depth (diagnostics). -/
  defEqPeak : UInt32 := 0
  /-- Shared recursive fuel remaining for this constant check. -/
  recFuel : UInt64 := maxRecFuel
  /-- Optional diagnostic label for the current top-level constant. -/
  debugLabel : Option String := none
  /-- Initial fuel restored by `reset` for each constant check (the
      `IX_MAX_REC_FUEL` override lands here via the driver). -/
  fuelBudget : UInt64 := maxRecFuel
  /-- Opt-in step journal (`IX_TC_STEP_TRACE`): `[deq]`/`[whnf+]` lines
      for the `debugLabel`ed constant only. See `TcM.stepTrace`. -/
  stepTrace : Bool := false
  /-- Opt-in counters (`IX_TC_STATS`); when false each bump site costs
      one state read + branch. -/
  stats : Bool := false
  /-- `isDefEq` calls (stats). -/
  deqCalls : UInt64 := 0
  /-- `isDefEq` calls that fell through every O(1) exit to structural
      work (stats); cache-hit rate = 1 − misses/calls. -/
  deqMisses : UInt64 := 0
  /-- `whnf` calls past the non-reducing quick exit (stats). -/
  whnfCalls : UInt64 := 0
  /-- `whnf` calls that missed the cache and did real work (stats). -/
  whnfMisses : UInt64 := 0
  /-- `synthCtorWhenK` candidates that reached the def-eq verify (stats). -/
  kSynthAttempts : UInt64 := 0
  /-- K-synthesis candidates the def-eq verify rejected — the silent
      fallback (stats; cross-kernel comparand of Rust `IX_KSYNTH_LOG`). -/
  kSynthRejects : UInt64 := 0
  /-- Disable the Ix-specific semantic shortcuts that have COMPLETE pure
      fallbacks — BitVec natives, Decidable natives, `Fin.val`-through-
      `Decidable.rec`, `reduceBool`/`reduceNat` markers — so accelerated
      and pure reduction can be differential-tested
      (`IX_TC_NO_ACCEL=1`). Deliberately does NOT gate Nat-literal or
      string-literal bridging: those are representation-level (the
      official kernel computes them natively) and the pure path cannot
      complete without them. Exponentially slow on large literals by
      design — use only on small seeded fixtures. -/
  noAccel : Bool := false
  /-- Current knot-dispatch depth (see `maxDispatchDepth`). -/
  dispatchDepth : UInt32 := 0
  /-- Memo for `ctxAddrForLbr`: pure in `(ctxId, lbr)`. -/
  ctxAddrCache : HashMap (Address × UInt64) Address := {}
  /-- Local context for fvar-based binder opening. -/
  lctx : LocalContext m := {}
  /-- Lazy on-demand ingress hook (Rust `LazyAnonIngress`): faults a missing
      constant's block into `env` by address. Installed by the driver
      (`TcState.newLazyAnon`); `none` for eagerly-ingressed envs. The closure
      runs against `env` and returns whether the address was found in the
      backing Ixon env. (The error type is `Ix.Tc.IngressErr`, spelled
      `String` here because `Ix.Tc.Ingress` imports this module.) -/
  lazyFault : Option (Address → EStateM String (KEnv m) Bool) := none
  /-- Addresses already faulted (hit or miss) — never re-ingress. Lives on
      the state (not reset per constant), mirroring Rust
      `LazyAnonIngress::faulted_addrs`. -/
  faultedAddrs : Std.HashSet Address := {}

namespace TcState

/-- Fresh state over `env` with explicitly resolved primitives. -/
def new (env : KEnv m) (prims : Primitives m) : TcState m :=
  { env, prims }

/-- Fresh state resolving primitives from the environment
    (mirrors `TypeChecker::new`). -/
def ofEnv (env : KEnv m) : TcState m :=
  { env, prims := .fromEnv env }

/-- Anon-mode state; primitive resolution needs no environment. -/
def ofEnvAnon (env : KEnv .anon) : TcState .anon :=
  { env, prims := .ofAnonAddrs }

end TcState

/-- The type-checking monad. -/
abbrev TcM (m : Mode) := EStateM (TcError m) (TcState m)

instance : Inhabited (TcM m α) := ⟨fun s => .error default s⟩

namespace TcM

@[inline] def ofExcept : Except (TcError m) α → TcM m α
  | .ok a => pure a
  | .error e => throw e

/-- Run an intern-table action against `env.intern`. -/
@[inline] def runIntern (x : InternM m α) : TcM m α := fun s =>
  let (a, it) := x s.env.intern
  .ok a { s with env := { s.env with intern := it } }

/-- Intern an expression (mirrors `TypeChecker::intern`). -/
@[inline] def intern (e : KExpr m) : TcM m (KExpr m) :=
  runIntern (internExprM e)

/-- Intern a universe. -/
@[inline] def internUniv (u : KUniv m) : TcM m (KUniv m) :=
  runIntern (internUnivM u)

@[inline] def modifyEnv (f : KEnv m → KEnv m) : TcM m Unit :=
  modify fun s => { s with env := f s.env }

/-- Run a mutating union-find operation on `equivManager` with unique
    ownership: swap the manager out of the state (leaving `{}`) for the
    duration so path-halving `Array.set!`s run in place. Extracting via
    `(← get).equivManager` leaves the state's reference alive (RC ≥ 2)
    and the `set!`s copy instead. Measured effect is small (the manager
    is reset per constant and stays modest-sized) — this is hygiene, not
    a hot-path win. `f` must be pure (must not throw) so the manager is
    always restored. -/
@[inline] def withEquiv (f : EquivManager → α × EquivManager) :
    TcM m α := do
  let em ← modifyGet fun s =>
    (s.equivManager, { s with equivManager := {} })
  let (a, em) := f em
  modify fun s => { s with equivManager := em }
  return a

/-- Consume one unit of shared recursive fuel. -/
@[inline] def tick : TcM m Unit := do
  let s ← get
  if s.recFuel == 0 then
    throw .maxRecFuel
  set { s with recFuel := s.recFuel - 1 }

/-- Fuel consumed so far in the current check. -/
def fuelUsed : TcM m UInt64 := do
  let s ← get
  return s.fuelBudget - s.recFuel

/-! ### Opt-in instrumentation (`IX_TC_STEP_TRACE` / `IX_TC_STATS`) -/

/-- First 8 hex chars of an address (step-journal rendering). -/
def addr8 (a : Address) : String := ((toString a).take 8).toString

/-- Emit one step-journal line — only when this constant is the debug
    target (`debugLabel`, set by the driver from `IX_TC_DEBUG_CONST`)
    and `stepTrace` is on (`IX_TC_STEP_TRACE=1`). `payload` is deferred,
    so an off switch costs one state read + branch. Line shape
    `[tag] <fuelUsed> <payload>` mirrors the Rust kernel's
    `IX_STEP_TRACE` journal; diffing the two sequences localizes a
    behavioral divergence at the first fork (workflow in
    `Ix.Tc.ParCheck`). -/
@[inline] def stepTrace (tag : String) (payload : Unit → String) :
    TcM m Unit := do
  let s ← get
  if s.stepTrace && s.debugLabel.isSome then
    let fuel := s.fuelBudget - s.recFuel
    dbgTrace s!"[{tag}] {fuel} {payload ()}" fun _ => pure ()

/-- Bump opt-in stats counters (no-op unless `stats`). -/
@[inline] def bumpStats (f : TcState m → TcState m) : TcM m Unit := do
  if (← get).stats then
    modify f

def freshFVarId : TcM m FVarId := fun s =>
  let (id, env) := s.env.freshFVarId
  .ok id { s with env }

/-- Fault `addr` through the lazy-ingress hook (if installed), deduplicated
    by `faultedAddrs`. Ingress errors surface as `TcError.other` with the
    Rust "lazy anon ingress" prefix. Mirrors tc.rs `lazy_ingress_addr`. -/
def lazyIngressAddr (addr : Address) : TcM m Unit := fun s =>
  match s.lazyFault with
  | none => .ok () s
  | some fault =>
    if s.faultedAddrs.contains addr then
      .ok () s
    else
      let s := { s with faultedAddrs := s.faultedAddrs.insert addr }
      match fault addr s.env with
      | .ok _ env => .ok () { s with env }
      | .error e env =>
        .error (.other s!"lazy anon ingress {addr}: {e}") { s with env }

/-- Constant lookup. On a miss with the lazy hook installed, faults the
    address and retries; a post-fault miss is a hard `unknownConst` (Rust
    parity: with lazy enabled, `try_get_const` errors rather than returning
    `none`). Without the hook, plain env read. -/
def tryGetConst (id : KId m) : TcM m (Option (KConst m)) := do
  if let some c := (← get).env.get? id then
    return some c
  let lazyEnabled := (← get).lazyFault.isSome
  lazyIngressAddr id.addr
  match (← get).env.get? id with
  | some c => return some c
  | none =>
    if lazyEnabled then
      throw (.unknownConst id.addr)
    return none

def getConst (id : KId m) : TcM m (KConst m) := do
  match (← tryGetConst id) with
  | some c => return c
  | none => throw (.unknownConst id.addr)

def hasConst (id : KId m) : TcM m Bool := do
  return (← tryGetConst id).isSome

/-- Block lookup with the same fault-on-miss behavior (a post-fault miss is
    `none`, not an error — mirrors tc.rs `try_get_block`). -/
def tryGetBlock (id : KId m) : TcM m (Option (Array (KId m))) := do
  if let some members := (← get).env.getBlock? id then
    return some members
  lazyIngressAddr id.addr
  return (← get).env.getBlock? id

/-! ### Context management -/

/-- Current logical binding depth: legacy de-Bruijn stack + opened fvars. -/
def depth : TcM m UInt64 := do
  let s ← get
  return (s.ctx.size + s.lctx.size).toUInt64

/-- Suffix-aware context identity for a loose-bound-variable range.

    Pure in `(ctxId, lbr)` (memoized). Runs a fixpoint closing the needed
    suffix over binder type/value dependencies, then hashes the suffix —
    unless the whole context is needed, in which case `ctxId` itself is the
    identity. Mirrors tc.rs `ctx_addr_for_lbr` exactly. -/
def ctxAddrForLbr (lbr : UInt64) : TcM m Address := do
  let s ← get
  if lbr == 0 || s.ctx.isEmpty then
    return emptyCtxAddr
  let cacheKey := (s.ctxId, lbr)
  if let some cached := s.ctxAddrCache[cacheKey]? then
    return cached
  let n := s.ctx.size
  let mut need := min lbr.toNat n
  repeat
    let start := n - need
    let mut nextNeed := need
    for i in [start:n] do
      let frameOffset := n - i
      let tyNeed := s.ctx[i]!.lbr.toNat
      nextNeed := max nextNeed (frameOffset + tyNeed)
      if let some val := s.letVals[i]! then
        nextNeed := max nextNeed (frameOffset + val.lbr.toNat)
    nextNeed := min nextNeed n
    if nextNeed == need then
      break
    need := nextNeed
  let result :=
    if need == n then s.ctxId
    else Id.run do
      let mut h := Blake3.Rust.Hasher.init ()
      h := h.update "ctx.suffix".toUTF8
      h := h.update (need.toUInt64.toLEBytes)
      for i in [n - need:n] do
        match s.letVals[i]! with
        | some val =>
          h := h.update "let".toUTF8
          h := h.update s.ctx[i]!.addr.hash
          h := h.update val.addr.hash
        | none =>
          h := h.update "local".toUTF8
          h := h.update s.ctx[i]!.addr.hash
      return ⟨(h.finalizeWithLength 32).val⟩
  modify fun s => { s with ctxAddrCache := s.ctxAddrCache.insert cacheKey result }
  return result

/-- WHNF cache key: `(exprAddr, ctxAddrForLbr e.lbr)`. Closed expressions
    collapse to the empty-context hash; open ones capture only the reachable
    context suffix. See tc.rs `whnf_key` for the soundness argument. -/
@[inline] def whnfKey (e : KExpr m) : TcM m (Address × Address) := do
  return (e.addr, ← ctxAddrForLbr e.lbr)

/-- Type-inference cache key; same shape as `whnfKey`. -/
@[inline] def inferKey (e : KExpr m) : TcM m (Address × Address) := do
  return (e.addr, ← ctxAddrForLbr e.lbr)

/-- Context key for a def-eq pair: the suffix needed by the larger `lbr`. -/
@[inline] def defEqCtxKey (a b : KExpr m) : TcM m Address :=
  ctxAddrForLbr (max a.lbr b.lbr)

/-- Push a lambda/forall-bound local (no let value). -/
def pushLocal (ty : KExpr m) : TcM m Unit := do
  let s ← get
  let ctxId : Address := Id.run do
    let mut h := Blake3.Rust.Hasher.init ()
    h := h.update "ctx.local".toUTF8
    h := h.update ty.addr.hash
    h := h.update s.ctxId.hash
    return ⟨(h.finalizeWithLength 32).val⟩
  set { s with
    ctxIdStack := s.ctxIdStack.push s.ctxId
    ctxId
    ctx := s.ctx.push ty
    letVals := s.letVals.push none }

/-- Push a let-bound local (type + value); WHNF zeta-reduces references to it. -/
def pushLet (ty val : KExpr m) : TcM m Unit := do
  let s ← get
  let ctxId : Address := Id.run do
    let mut h := Blake3.Rust.Hasher.init ()
    h := h.update "ctx.let".toUTF8
    h := h.update ty.addr.hash
    h := h.update val.addr.hash
    h := h.update s.ctxId.hash
    return ⟨(h.finalizeWithLength 32).val⟩
  set { s with
    ctxIdStack := s.ctxIdStack.push s.ctxId
    ctxId
    ctx := s.ctx.push ty
    letVals := s.letVals.push (some val)
    numLetBindings := s.numLetBindings + 1 }

/-- Pop the most recent local. -/
def popLocal : TcM m Unit := do
  let s ← get
  let numLetBindings :=
    match s.letVals.back? with
    | some (some _) => s.numLetBindings - 1
    | _ => s.numLetBindings
  set { s with
    ctx := s.ctx.pop
    letVals := s.letVals.pop
    numLetBindings
    ctxId := s.ctxIdStack.back?.getD emptyCtxAddr
    ctxIdStack := s.ctxIdStack.pop }

/-- Let-bound value of variable `idx`, lifted to the current depth; `none`
    for lambda/forall frames or out-of-range. -/
def lookupLetVal (idx : UInt64) : TcM m (Option (KExpr m)) := do
  let s ← get
  let n := s.ctx.size
  if idx.toNat ≥ n then
    return none
  let level := n - 1 - idx.toNat
  match s.letVals[level]! with
  | none => return none
  | some val => return some (← runIntern (lift val (idx + 1) 0))

/-- Whether a de-Bruijn variable points at a let-bound local. -/
def isLetVar (idx : UInt64) : TcM m Bool := do
  let s ← get
  let n := s.ctx.size
  if idx.toNat ≥ n then
    return false
  return s.letVals[n - 1 - idx.toNat]!.isSome

/-- Save the legacy ctx depth for later restore. -/
def saveDepth : TcM m Nat := do
  return (← get).ctx.size

/-- Restore the legacy ctx to a saved depth. -/
def restoreDepth (saved : Nat) : TcM m Unit := do
  while (← get).ctx.size > saved do
    popLocal

/-- Bound variable's type, lifted to the current depth. -/
def lookupVar (idx : UInt64) : TcM m (KExpr m) := do
  let s ← get
  let n := s.ctx.size
  if idx.toNat ≥ n then
    throw (.varOutOfRange idx n)
  let ty := s.ctx[n - 1 - idx.toNat]!
  runIntern (lift ty (idx + 1) 0)

/-! ### Free-variable binder opening -/

/-- Open a binder: mint a fresh fvar, push a `cdecl`, instantiate `body` so
    `Var(0)` becomes the fvar. The caller is responsible for
    `lctx.truncate` when leaving the scope. -/
def openBinder (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty : KExpr m)
    (body : KExpr m) : TcM m (KExpr m × FVarId) := do
  let fvId ← freshFVarId
  let fv ← intern (KExpr.mkFVar fvId name)
  modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty) }
  let bodyOpen ← runIntern (instantiateRev body #[fv])
  return (bodyOpen, fvId)

/-- Anonymous-name variant of `openBinder`. -/
def openBinderAnon (ty : KExpr m) (body : KExpr m) :
    TcM m (KExpr m × FVarId) :=
  openBinder (Mode.fieldWith fun _ => .mkAnon)
    (Mode.fieldWith fun _ => .default) ty body

/-- Like `openBinder` but also returns the fvar expression itself. -/
def openBinderWithFV (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty : KExpr m) (body : KExpr m) : TcM m (KExpr m × KExpr m × FVarId) := do
  let fvId ← freshFVarId
  let fv ← intern (KExpr.mkFVar fvId name)
  modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty) }
  let bodyOpen ← runIntern (instantiateRev body #[fv])
  return (bodyOpen, fv, fvId)

/-- Anonymous-name variant of `openBinderWithFV`. -/
def openBinderAnonWithFV (ty : KExpr m) (body : KExpr m) :
    TcM m (KExpr m × KExpr m × FVarId) :=
  openBinderWithFV (Mode.fieldWith fun _ => .mkAnon)
    (Mode.fieldWith fun _ => .default) ty body

/-- Push an `ldecl` for a let-bound fvar and instantiate the body. -/
def openLet (name : m.F Name) (ty val : KExpr m) (body : KExpr m) :
    TcM m (KExpr m × FVarId) := do
  let fvId ← freshFVarId
  let fv ← intern (KExpr.mkFVar fvId name)
  modify fun s => { s with lctx := s.lctx.push fvId (.ldecl name ty val) }
  let bodyOpen ← runIntern (instantiateRev body #[fv])
  return (bodyOpen, fvId)

/-- Push a fresh fvar declaration without a body to instantiate. -/
def pushFVarDeclAnon (ty : KExpr m) : TcM m (FVarId × KExpr m) := do
  let name : m.F Name := Mode.fieldWith fun _ => .mkAnon
  let bi : m.F Lean.BinderInfo := Mode.fieldWith fun _ => .default
  let fvId ← freshFVarId
  let fv ← intern (KExpr.mkFVar fvId name)
  modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty) }
  return (fvId, fv)

/-! ### Universe helpers -/

/-- Substitute universe params in a level: `param i ↦ us[i]`. Errors with
    `univParamOutOfRange` as defense-in-depth (arity is validated upstream at
    const-infer time). -/
def substUniv (u : KUniv m) (us : Array (KUniv m)) :
    Except (TcError m) (KUniv m) :=
  match u with
  | .zero _ => .ok u
  | .param i _ _ =>
    match us[i.toNat]? with
    | some v => .ok v
    | none => .error (.univParamOutOfRange i us.size)
  | .succ inner _ => do
    return .mkSucc (← substUniv inner us)
  | .max a b _ => do
    return .mkMax (← substUniv a us) (← substUniv b us)
  | .imax a b _ => do
    return .mkIMax (← substUniv a us) (← substUniv b us)

def instUnivInner (e : KExpr m) (us : Array (KUniv m)) :
    StateT (HashMap Address (KExpr m)) (TcM m) (KExpr m) := do
  -- Key by content hash only — `us` is fixed across the whole call.
  let key := e.addr
  if let some cached := (← get)[key]? then
    return cached
  let result ← match e with
    | .var .. | .fvar .. | .nat .. | .str .. => do
      -- No universe parameters; cache the pass-through.
      modify (·.insert key e)
      return e
    -- `pure`, not `return`, in every rebuilding arm: `return` exits the
    -- whole function, skipping the intern + memo-insert tail below, and
    -- an interior-node-less memo turns shared-DAG walks exponential
    -- (see the note in `Ix/Tc/Subst.lean` `liftCached`).
    | .sort u _ =>
      pure (KExpr.mkSort (← TcM.ofExcept (substUniv u us)))
    | .const id curUs _ => do
      let mut newUs : Array (KUniv m) := Array.mkEmpty curUs.size
      for u in curUs do
        newUs := newUs.push (← TcM.ofExcept (substUniv u us))
      pure (KExpr.mkConst id newUs)
    | .app f a _ =>
      pure (KExpr.mkApp (← instUnivInner f us) (← instUnivInner a us))
    | .lam name bi ty body _ =>
      pure (KExpr.mkLam name bi (← instUnivInner ty us)
        (← instUnivInner body us))
    | .all name bi ty body _ =>
      pure (KExpr.mkAll name bi (← instUnivInner ty us)
        (← instUnivInner body us))
    | .letE name ty val body nd _ =>
      pure (KExpr.mkLet name (← instUnivInner ty us)
        (← instUnivInner val us) (← instUnivInner body us) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← instUnivInner val us))
  let interned ← TcM.intern result
  modify (·.insert key interned)
  return interned
termination_by structural e

/-- Substitute universe parameters throughout an expression, with per-call
    address-keyed memoization (universe substitution doesn't change binder
    structure, so depth is not part of the key). -/
def instantiateUnivParams (e : KExpr m) (us : Array (KUniv m)) :
    TcM m (KExpr m) := do
  if us.isEmpty then
    return e
  (instUnivInner e us).run' {}

/-! ### Per-constant reset and modes -/

/-- Reset per-check state between constants. Global caches in `KEnv` are NOT
    cleared (they grow monotonically); the env-level fvar counter is
    intentionally NOT reset (open-term cache soundness across checkers). -/
def reset : TcM m Unit := do
  modify fun s => { s with
    ctx := #[]
    letVals := #[]
    numLetBindings := 0
    ctxId := emptyCtxAddr
    ctxIdStack := #[]
    equivManager := {}
    inferOnly := false
    inNativeReduce := false
    cheapRecursionDepth := 0
    eagerReduce := false
    defEqDepth := 0
    defEqPeak := 0
    dispatchDepth := 0
    recFuel := s.fuelBudget
    ctxAddrCache := {}
    lctx := {} }

def setDebugLabel (label : String) : TcM m Unit :=
  modify fun s => { s with debugLabel := some label }

/-- Run `f` with `inferOnly` enabled, restoring the previous mode on exit
    (also on error — Rust restores after the closure regardless). -/
def withInferOnly (f : TcM m α) : TcM m α := do
  let prev := (← get).inferOnly
  modify fun s => { s with inferOnly := true }
  try
    f
  finally
    modify fun s => { s with inferOnly := prev }

/-- Is `e` of the form `eagerReduce _ _` (exactly two args on the marker)? -/
def isEagerReduce (e : KExpr m) : TcM m Bool := do
  let (head, args) := e.collectSpine
  if args.size != 2 then
    return false
  match head with
  | .const id _ _ => return id.addr == (← get).prims.eagerReduce.addr
  | _ => return false

end TcM

/-! ### Free-standing helpers (tc.rs) -/

/-- Does `e` mention a constant with the given address? Iterative
    (stack-based) — immune to stack overflow on deep input. -/
def exprMentionsAddr (e : KExpr m) (addr : Address) : Bool := Id.run do
  let mut stack : Array (KExpr m) := #[e]
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    match e with
    | .const id _ _ =>
      if id.addr == addr then
        return true
    | .app f a _ =>
      stack := stack.push f |>.push a
    | .lam _ _ ty body _ | .all _ _ ty body _ =>
      stack := stack.push ty |>.push body
    | .letE _ ty val body _ _ =>
      stack := stack.push ty |>.push val |>.push body
    | .prj id _ val _ =>
      if id.addr == addr then
        return true
      stack := stack.push val
    | _ => pure ()
  return false

/-- Does `e` mention any constant from `addrs`? -/
def exprMentionsAnyAddr (e : KExpr m) (addrs : Array Address) : Bool :=
  addrs.any (exprMentionsAddr e)

/-! ### The recursion knot -/

/-- Back-edges of the whnf ↔ infer ↔ def-eq recursion. Whnf reads
    `infer`/`isDefEq`; Infer imports Whnf directly; DefEq imports both. The
    knot is tied by one `partial def` in `Ix.Tc.Knot`. -/
structure Methods (m : Mode) where
  whnf : KExpr m → TcM m (KExpr m)
  whnfCore : KExpr m → TcM m (KExpr m)
  infer : KExpr m → TcM m (KExpr m)
  isDefEq : KExpr m → KExpr m → TcM m Bool

instance : Inhabited (Methods m) where
  default :=
    { whnf := fun _ => throw (.other "Methods.whnf: knot not tied")
      whnfCore := fun _ => throw (.other "Methods.whnfCore: knot not tied")
      infer := fun _ => throw (.other "Methods.infer: knot not tied")
      isDefEq := fun _ _ => throw (.other "Methods.isDefEq: knot not tied") }

/-- `TcM` with the recursion back-edges in scope. -/
abbrev RecM (m : Mode) := ReaderT (Methods m) (TcM m)

/-- Dispatch-depth ceiling across the four knot back-edges: a clean
    rejection far before a would-be native stack overflow. Corpus-legal
    depths are tiny (per-item `defEqPeak` ≤ ~54 across the InitStd and
    Lean tiers); the pre-subst-fix pathologies were ~30k native frames;
    the 256 MB worker stacks hold well past 200k dispatch frames. The
    Rust mirror has no analogous guard (its stacks + fuel bound it) —
    this is Lean-side hardening only, so the limit MUST stay far above
    any legitimate depth to remain verdict-neutral; a trip is an
    infra-style `.other` error, deliberately NOT `.maxRecDepth` (a
    Rust-parity verdict). -/
def maxDispatchDepth : UInt32 := 200_000

namespace RecM

/-- Enter one knot dispatch: bump the depth, trip past the ceiling.
    Callers pair with `exitDispatch` via `try/finally` (balanced on
    error unwinds). -/
@[inline] def enterDispatch : TcM m Unit := do
  let s ← get
  let d := s.dispatchDepth + 1
  if d > maxDispatchDepth then
    throw (.other s!"dispatch depth exceeded {maxDispatchDepth} \
                    (would overflow the worker stack)")
  set { s with dispatchDepth := d }

@[inline] def exitDispatch : TcM m Unit :=
  modify fun s => { s with dispatchDepth := s.dispatchDepth - 1 }

@[inline] def callWhnf (e : KExpr m) : RecM m (KExpr m) := do
  enterDispatch (m := m)
  try (← read).whnf e
  finally exitDispatch (m := m)

@[inline] def callWhnfCore (e : KExpr m) : RecM m (KExpr m) := do
  enterDispatch (m := m)
  try (← read).whnfCore e
  finally exitDispatch (m := m)

@[inline] def callInfer (e : KExpr m) : RecM m (KExpr m) := do
  enterDispatch (m := m)
  try (← read).infer e
  finally exitDispatch (m := m)

@[inline] def callIsDefEq (a b : KExpr m) : RecM m Bool := do
  enterDispatch (m := m)
  try (← read).isDefEq a b
  finally exitDispatch (m := m)

/-- WHNF, then ensure a `sort`; returns the universe. Fast path skips WHNF
    when the node is already a sort. -/
def ensureSort (e : KExpr m) : RecM m (KUniv m) := do
  if let .sort u _ := e then
    return u
  match (← callWhnf e) with
  | .sort u _ => return u
  | _ => throw .typeExpected

/-- WHNF, then ensure a forall; returns (domain, codomain). -/
def ensureForall (e : KExpr m) : RecM m (KExpr m × KExpr m) := do
  if let .all _ _ a b _ := e then
    return (a, b)
  let w ← callWhnf e
  match w with
  | .all _ _ a b _ => return (a, b)
  | _ => throw (.funExpected e w)

end RecM

end Ix.Tc

end
end
