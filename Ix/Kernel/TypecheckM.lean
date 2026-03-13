/-
  Kernel2 TypecheckM: Monad stack, context, state, and thunk operations.

  All mutable state lives in ST.Ref fields within the reader context.
  Monad is ReaderT + ExceptT + ST (no StateT — all mutation via ST.Ref).
  σ parameterizes the ST region — runST at the top level keeps everything pure.
  Context stores types as Val (indexed by de Bruijn level, not index).
-/
import Ix.Kernel.Value
import Ix.Kernel.EquivManager
import Ix.Kernel.Datatypes
import Ix.Kernel.Level
import Std.Data.HashMap
import Init.System.ST

namespace Ix.Kernel

-- Additional K-abbreviations for types from Datatypes.lean
abbrev KTypedConst (m : Ix.Kernel.MetaMode) := Ix.Kernel.TypedConst m
abbrev KTypedExpr (m : Ix.Kernel.MetaMode) := Ix.Kernel.TypedExpr m
abbrev KTypeInfo (m : Ix.Kernel.MetaMode) := Ix.Kernel.TypeInfo m

/-! ## Thunk entry

Stored in the thunk table (external to Val). Each thunk is either unevaluated
(an Expr + closure env) or evaluated (a Val). ST.Ref mutation gives call-by-need. -/

inductive ThunkEntry (m : Ix.Kernel.MetaMode) : Type where
  | unevaluated (expr : KExpr m) (env : Array (Val m))
  | evaluated (val : Val m)

/-! ## Stats -/

/-- Performance counters for the type checker. -/
structure Stats where
  heartbeats      : Nat := 0
  inferCalls      : Nat := 0
  evalCalls       : Nat := 0
  forceCalls      : Nat := 0
  isDefEqCalls    : Nat := 0
  thunkCount      : Nat := 0
  thunkForces     : Nat := 0
  thunkHits       : Nat := 0
  cacheHits       : Nat := 0
  deltaSteps      : Nat := 0
  nativeReduces   : Nat := 0
  whnfCacheMisses : Nat := 0
  proofIrrelHits  : Nat := 0
  -- isDefEq breakdown
  quickTrue       : Nat := 0
  quickFalse      : Nat := 0
  equivHits       : Nat := 0
  ptrSuccessHits  : Nat := 0
  ptrFailureHits  : Nat := 0
  step10Fires     : Nat := 0
  step11Fires     : Nat := 0
  -- whnf breakdown
  whnfCacheHits   : Nat := 0
  whnfEquivHits   : Nat := 0
  whnfCoreCacheHits   : Nat := 0
  whnfCoreCacheMisses : Nat := 0
  -- delta breakdown
  lazyDeltaIters  : Nat := 0
  sameHeadChecks  : Nat := 0
  sameHeadHits    : Nat := 0
  deriving Inhabited

/-! ## Typechecker Context

All mutable state lives as ST.Ref fields in the reader context.
This eliminates StateT from the monad stack — all mutation is via ST.Ref. -/

def defaultMaxHeartbeats : Nat := 200_000_000
def defaultMaxThunks : Nat := 10_000_000

structure TypecheckCtx (σ : Type) (m : Ix.Kernel.MetaMode) where
  -- Immutable context (changed only via withReader)
  types      : Array (Val m)
  letValues  : Array (Option (Val m)) := #[]
  binderNames : Array (KMetaField m Ix.Name) := #[]
  kenv       : KEnv m
  prims      : KPrimitives m
  safety     : KDefinitionSafety
  quotInit   : Bool
  mutTypes   : Std.TreeMap Nat (KMetaId m × (Array (KLevel m) → Val m)) compare := default
  recId?     : Option (KMetaId m) := none
  inferOnly  : Bool := false
  eagerReduce : Bool := false
  wordSize   : WordSize := .word64
  trace      : Bool := false
  maxHeartbeats : Nat := defaultMaxHeartbeats
  maxThunks  : Nat := defaultMaxThunks
  -- Mutable refs (all mutation via ST.Ref — no StateT needed)
  thunkTable       : ST.Ref σ (Array (ThunkEntry m))
  statsRef         : ST.Ref σ Stats
  typedConstsRef   : ST.Ref σ (Std.HashMap (KMetaId m) (KTypedConst m))
  ptrFailureCacheRef : ST.Ref σ (Std.HashMap (USize × USize) (Val m × Val m))
  ptrSuccessCacheRef : ST.Ref σ (Std.HashMap (USize × USize) (Val m × Val m))
  eqvManagerRef    : ST.Ref σ EquivManager
  keepAliveRef     : ST.Ref σ (Array (Val m))
  inferCacheRef    : ST.Ref σ (Std.HashMap USize (KExpr m × Array (Val m) × KTypedExpr m × Val m))
  whnfCacheRef     : ST.Ref σ (Std.HashMap USize (Val m × Val m))
  whnfCoreCacheRef : ST.Ref σ (Std.HashMap USize (Val m × Val m))

/-! ## TypecheckM monad

  ReaderT for context (immutable fields + mutable ST.Ref fields).
  ExceptT for errors, ST for mutable refs.
  No StateT — all mutation via ST.Ref in the context. -/

abbrev TypecheckM (σ : Type) (m : Ix.Kernel.MetaMode) :=
  ReaderT (TypecheckCtx σ m) (ExceptT String (ST σ))

/-! ## Thunk operations -/

/-- Allocate a new thunk (unevaluated). Returns its index. -/
@[inline] def mkThunk (expr : KExpr m) (env : Array (Val m)) : TypecheckM σ m Nat := do
  let ctx ← read
  ctx.statsRef.modify fun s => { s with thunkCount := s.thunkCount + 1 }
  let size ← ctx.thunkTable.modifyGet fun table =>
    (table.size, table.push (.unevaluated expr env))
  if size >= ctx.maxThunks then
    throw s!"thunk table limit exceeded ({size})"
  pure size

/-- Allocate a thunk that is already evaluated. -/
@[inline] def mkThunkFromVal (v : Val m) : TypecheckM σ m Nat := do
  let ctx ← read
  ctx.statsRef.modify fun s => { s with thunkCount := s.thunkCount + 1 }
  let size ← ctx.thunkTable.modifyGet fun table =>
    (table.size, table.push (.evaluated v))
  if size >= ctx.maxThunks then
    throw s!"thunk table limit exceeded ({size})"
  pure size

/-- Read a thunk entry without forcing (for inspection). -/
@[inline] def peekThunk (id : Nat) : TypecheckM σ m (ThunkEntry m) := do
  let table ← (← read).thunkTable.get
  if h : id < table.size then
    pure table[id]
  else
    throw s!"thunk id {id} out of bounds (table size {table.size})"

/-- Check if a thunk has been evaluated. -/
def isThunkEvaluated (id : Nat) : TypecheckM σ m Bool := do
  match ← peekThunk id with
  | .evaluated _ => pure true
  | .unevaluated _ _ => pure false

/-! ## Context helpers -/

@[inline] def depth : TypecheckM σ m Nat := do pure (← read).types.size

def withResetCtx : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with
    types := #[], letValues := #[], binderNames := #[],
    mutTypes := default, recId? := none }

def withBinder (varType : Val m) (name : KMetaField m Ix.Name := default)
    : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with
    types := ctx.types.push varType,
    letValues := ctx.letValues.push none,
    binderNames := ctx.binderNames.push name }

def withLetBinder (varType : Val m) (val : Val m) (name : KMetaField m Ix.Name := default)
    : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with
    types := ctx.types.push varType,
    letValues := ctx.letValues.push (some val),
    binderNames := ctx.binderNames.push name }

def withMutTypes (mutTypes : Std.TreeMap Nat (KMetaId m × (Array (KLevel m) → Val m)) compare) :
    TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

def withRecId (id : KMetaId m) : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with recId? := some id }

def withInferOnly : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with inferOnly := true }

def withSafety (s : KDefinitionSafety) : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with safety := s }

@[inline] def mkFreshFVar (ty : Val m) : TypecheckM σ m (Val m) := do
  let d ← depth
  pure (Val.mkFVar d ty)

/-! ## EquivManager helpers (direct ST.Ref access — no StateT overhead) -/

@[inline] def equivIsEquiv (ptr1 ptr2 : USize) : TypecheckM σ m Bool := do
  if ptr1 == ptr2 then return true
  let ref := (← read).eqvManagerRef
  let mgr ← ref.get
  match mgr.toNodeMap.get? ptr1, mgr.toNodeMap.get? ptr2 with
  | some n1, some n2 =>
    let (uf', r1) := mgr.uf.findD n1
    let (uf'', r2) := uf'.findD n2
    ref.set { mgr with uf := uf'' }
    return r1 == r2
  | _, _ => return false

@[inline] def equivAddEquiv (ptr1 ptr2 : USize) : TypecheckM σ m Unit := do
  let ref := (← read).eqvManagerRef
  let mgr ← ref.get
  let (_, mgr') := EquivManager.addEquiv ptr1 ptr2 |>.run mgr
  ref.set mgr'

@[inline] def equivFindRootPtr (ptr : USize) : TypecheckM σ m (Option USize) := do
  let ref := (← read).eqvManagerRef
  let mgr ← ref.get
  match mgr.toNodeMap.get? ptr with
  | none => return none
  | some n =>
    let (uf', root) := mgr.uf.findD n
    let mgr' := { mgr with uf := uf' }
    ref.set mgr'
    if h : root < mgr'.nodeToPtr.size then
      return some mgr'.nodeToPtr[root]
    else
      return some ptr

/-! ## Heartbeat -/

/-- Increment heartbeat counter. Called at every operation entry point
    (eval, whnfCoreVal, forceThunk, lazyDelta step, infer, isDefEq)
    to bound total work. -/
@[inline] def heartbeat : TypecheckM σ m Unit := do
  let ctx ← read
  let stats ← ctx.statsRef.get
  if stats.heartbeats >= ctx.maxHeartbeats then
    throw s!"heartbeat limit exceeded ({ctx.maxHeartbeats})"
  let hb := stats.heartbeats + 1
  if ctx.trace && hb % 100_000 == 0 then
    let table ← ctx.thunkTable.get
    dbg_trace s!"    [hb] {hb / 1000}K heartbeats, delta={stats.deltaSteps}, thunkTable={table.size}, isDefEq={stats.isDefEqCalls}, eval={stats.evalCalls}, force={stats.forceCalls}"
  ctx.statsRef.set { stats with heartbeats := hb }

/-! ## Const dereferencing -/

def derefConst (id : KMetaId m) : TypecheckM σ m (KConstantInfo m) := do
  match (← read).kenv.find? id with
  | some ci => pure ci
  | none => throw s!"unknown constant {id}"

def derefConstByAddr (addr : Address) : TypecheckM σ m (KConstantInfo m) := do
  match (← read).kenv.findByAddr? addr with
  | some ci => pure ci
  | none => throw s!"unknown constant {addr}"

def derefTypedConst (id : KMetaId m) : TypecheckM σ m (KTypedConst m) := do
  match (← (← read).typedConstsRef.get).get? id with
  | some tc => pure tc
  | none => throw s!"typed constant not found: {id}"

def lookupName (id : KMetaId m) : TypecheckM σ m (KMetaField m Ix.Name) := do
  match (← read).kenv.find? id with
  | some ci => pure ci.cv.name
  | none => pure default

/-! ## Provisional TypedConst -/

def getMajorInductId (type : KExpr m) (numParams numMotives numMinors numIndices : Nat)
    : Option (KMetaId m) :=
  go (numParams + numMotives + numMinors + numIndices) type
where
  go : Nat → KExpr m → Option (KMetaId m)
    | 0, e => match e with
      | .forallE dom _ _ _ => match dom.getAppFn with
        | .const id _ => some id
        | _ => none
      | _ => none
    | n+1, e => match e with
      | .forallE _ body _ _ => go n body
      | _ => none

def provisionalTypedConst (ci : KConstantInfo m) : KTypedConst m :=
  let rawType : KTypedExpr m := ⟨default, ci.type⟩
  match ci with
  | .axiomInfo _ => .axiom rawType
  | .thmInfo v => .theorem rawType ⟨default, v.value⟩
  | .defnInfo v =>
    .definition rawType ⟨default, v.value⟩ (v.safety == .partial)
  | .opaqueInfo v => .opaque rawType ⟨default, v.value⟩
  | .quotInfo v => .quotient rawType v.kind
  | .inductInfo v =>
    let isStruct := v.ctors.size == 1
    .inductive rawType isStruct
  | .ctorInfo v => .constructor rawType v.cidx v.numFields
  | .recInfo v =>
    let indAddr := (getMajorInductId ci.type v.numParams v.numMotives v.numMinors v.numIndices).map (·.addr)
      |>.getD default
    let typedRules := v.rules.map fun r => (r.nfields, (⟨default, r.rhs⟩ : KTypedExpr m))
    .recursor rawType v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules

def ensureTypedConst (id : KMetaId m) : TypecheckM σ m Unit := do
  let ref := (← read).typedConstsRef
  if (← ref.get).get? id |>.isSome then return ()
  let ci ← derefConst id
  let tc := provisionalTypedConst ci
  ref.modify fun m => m.insert id tc

/-! ## Top-level runner -/

/-- Create all ST.Ref fields and build a default TypecheckCtx. -/
private def mkCtxST (σ : Type) (kenv : KEnv m) (prims : KPrimitives m)
    (safety : KDefinitionSafety := .safe) (quotInit : Bool := false)
    (trace : Bool := false) (maxHeartbeats : Nat := defaultMaxHeartbeats)
    (maxThunks : Nat := defaultMaxThunks) : ST σ (TypecheckCtx σ m) := do
  let thunkTable ← ST.mkRef (#[] : Array (ThunkEntry m))
  let statsRef ← ST.mkRef ({} : Stats)
  let typedConstsRef ← ST.mkRef ({} : Std.HashMap (KMetaId m) (KTypedConst m))
  let ptrFailureCacheRef ← ST.mkRef ({} : Std.HashMap (USize × USize) (Val m × Val m))
  let ptrSuccessCacheRef ← ST.mkRef ({} : Std.HashMap (USize × USize) (Val m × Val m))
  let eqvManagerRef ← ST.mkRef ({} : EquivManager)
  let keepAliveRef ← ST.mkRef (#[] : Array (Val m))
  let inferCacheRef ← ST.mkRef ({} : Std.HashMap USize (KExpr m × Array (Val m) × KTypedExpr m × Val m))
  let whnfCacheRef ← ST.mkRef ({} : Std.HashMap USize (Val m × Val m))
  let whnfCoreCacheRef ← ST.mkRef ({} : Std.HashMap USize (Val m × Val m))
  pure {
    types := #[], kenv, prims, safety, quotInit, trace, maxHeartbeats, maxThunks,
    thunkTable, statsRef, typedConstsRef, ptrFailureCacheRef, ptrSuccessCacheRef,
    eqvManagerRef, keepAliveRef, inferCacheRef, whnfCacheRef, whnfCoreCacheRef }

/-- Run a TypecheckM computation purely via runST.
    Everything runs inside a single ST σ region. -/
def TypecheckM.runSimple (kenv : KEnv m) (prims : KPrimitives m)
    (safety : KDefinitionSafety := .safe) (quotInit : Bool := false)
    (trace : Bool := false) (maxHeartbeats : Nat := defaultMaxHeartbeats)
    (maxThunks : Nat := defaultMaxThunks)
    (action : ∀ σ, TypecheckM σ m α)
    : Except String α :=
  runST fun σ => do
    let ctx ← mkCtxST σ kenv prims safety quotInit trace maxHeartbeats maxThunks
    ExceptT.run (ReaderT.run (action σ) ctx)

/-- Run and return stats alongside the result. Stats are always available
    (even on error) since they live in ST.Ref, not StateT. -/
def TypecheckM.runWithStats (kenv : KEnv m) (prims : KPrimitives m)
    (safety : KDefinitionSafety := .safe) (quotInit : Bool := false)
    (trace : Bool := false) (maxHeartbeats : Nat := defaultMaxHeartbeats)
    (maxThunks : Nat := defaultMaxThunks)
    (action : ∀ σ, TypecheckM σ m α)
    : Option String × Stats :=
  runST fun σ => do
    let ctx ← mkCtxST σ kenv prims safety quotInit trace maxHeartbeats maxThunks
    let result ← ExceptT.run (ReaderT.run (action σ) ctx)
    let stats ← ctx.statsRef.get
    match result with
    | .ok _ => pure (none, stats)
    | .error e => pure (some e, stats)

end Ix.Kernel
