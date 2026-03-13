/-
  Kernel2 TypecheckM: Monad stack, context, state, and thunk operations.

  Monad is based on EST (ExceptT + ST) for pure mutable references.
  σ parameterizes the ST region — runEST at the top level keeps everything pure.
  Context stores types as Val (indexed by de Bruijn level, not index).
  Thunk table lives in the reader context (ST.Ref identity doesn't change).
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

/-- Performance counters for the type checker. Defined early so it can be
    referenced in TypecheckCtx (for the stats snapshot ref). -/
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

/-! ## Typechecker Context -/

structure TypecheckCtx (σ : Type) (m : Ix.Kernel.MetaMode) where
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
  -- Thunk table: ST.Ref to array of ST.Ref thunk entries
  thunkTable : ST.Ref σ (Array (ST.Ref σ (ThunkEntry m)))
  -- Optional stats snapshot: heartbeat saves stats here before throwing.
  statsSnapshot : Option (ST.Ref σ Stats) := none

/-! ## Typechecker State -/

def defaultMaxHeartbeats : Nat := 200_000_000
def defaultMaxThunks : Nat := 10_000_000

structure TypecheckState (m : Ix.Kernel.MetaMode) where
  typedConsts    : Std.HashMap (KMetaId m) (KTypedConst m) := {}
  ptrFailureCache : Std.HashMap (USize × USize) (Val m × Val m) := {}
  ptrSuccessCache : Std.HashMap (USize × USize) (Val m × Val m) := {}
  eqvManager     : EquivManager := {}
  keepAlive      : Array (Val m) := #[]
  inferCache     : Std.HashMap USize (KExpr m × Array (Val m) × KTypedExpr m × Val m) := {}
  whnfCache      : Std.HashMap USize (Val m × Val m) := {}
  whnfCoreCache  : Std.HashMap USize (Val m × Val m) := {}
  maxHeartbeats  : Nat := defaultMaxHeartbeats
  maxThunks      : Nat := defaultMaxThunks
  stats          : Stats := {}
  deriving Inhabited

/-! ## TypecheckM monad

  ReaderT for immutable context (including thunk table ref).
  StateT for mutable counters/caches (typedConsts, heartbeats, etc.).
  ExceptT for errors, ST for mutable thunk refs. -/

abbrev TypecheckM (σ : Type) (m : Ix.Kernel.MetaMode) :=
  ReaderT (TypecheckCtx σ m) (StateT (TypecheckState m) (ExceptT String (ST σ)))

/-! ## Thunk operations -/

/-- Allocate a new thunk (unevaluated). Returns its index. -/
def mkThunk (expr : KExpr m) (env : Array (Val m)) : TypecheckM σ m Nat := do
  modify fun st => { st with stats.thunkCount := st.stats.thunkCount + 1 }
  let tableRef := (← read).thunkTable
  let table ← tableRef.get
  if table.size >= (← get).maxThunks then
    throw s!"thunk table limit exceeded ({table.size})"
  let entryRef ← ST.mkRef (ThunkEntry.unevaluated expr env)
  tableRef.set (table.push entryRef)
  pure table.size

/-- Allocate a thunk that is already evaluated. -/
def mkThunkFromVal (v : Val m) : TypecheckM σ m Nat := do
  modify fun st => { st with stats.thunkCount := st.stats.thunkCount + 1 }
  let tableRef := (← read).thunkTable
  let table ← tableRef.get
  if table.size >= (← get).maxThunks then
    throw s!"thunk table limit exceeded ({table.size})"
  let entryRef ← ST.mkRef (ThunkEntry.evaluated v)
  tableRef.set (table.push entryRef)
  pure table.size

/-- Read a thunk entry without forcing (for inspection). -/
def peekThunk (id : Nat) : TypecheckM σ m (ThunkEntry m) := do
  let tableRef := (← read).thunkTable
  let table ← tableRef.get
  if h : id < table.size then
    ST.Ref.get table[id]
  else
    throw s!"thunk id {id} out of bounds (table size {table.size})"

/-- Check if a thunk has been evaluated. -/
def isThunkEvaluated (id : Nat) : TypecheckM σ m Bool := do
  match ← peekThunk id with
  | .evaluated _ => pure true
  | .unevaluated _ _ => pure false

/-! ## Context helpers -/

def depth : TypecheckM σ m Nat := do pure (← read).types.size

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

def mkFreshFVar (ty : Val m) : TypecheckM σ m (Val m) := do
  let d ← depth
  pure (Val.mkFVar d ty)

/-! ## EquivManager helpers (avoid StateM overhead) -/

@[inline] def equivIsEquiv (ptr1 ptr2 : USize) : TypecheckM σ m Bool := do
  if ptr1 == ptr2 then return true
  let stt ← get
  let mgr := stt.eqvManager
  match mgr.toNodeMap.get? ptr1, mgr.toNodeMap.get? ptr2 with
  | some n1, some n2 =>
    let (uf', r1) := mgr.uf.findD n1
    let (uf'', r2) := uf'.findD n2
    modify fun st => { st with eqvManager := { mgr with uf := uf'' } }
    return r1 == r2
  | _, _ => return false

@[inline] def equivAddEquiv (ptr1 ptr2 : USize) : TypecheckM σ m Unit := do
  let stt ← get
  let (_, mgr') := EquivManager.addEquiv ptr1 ptr2 |>.run stt.eqvManager
  modify fun st => { st with eqvManager := mgr' }

@[inline] def equivFindRootPtr (ptr : USize) : TypecheckM σ m (Option USize) := do
  let stt ← get
  let mgr := stt.eqvManager
  match mgr.toNodeMap.get? ptr with
  | none => return none
  | some n =>
    let (uf', root) := mgr.uf.findD n
    let mgr' := { mgr with uf := uf' }
    modify fun st => { st with eqvManager := mgr' }
    if h : root < mgr'.nodeToPtr.size then
      return some mgr'.nodeToPtr[root]
    else
      return some ptr

/-! ## Heartbeat -/

/-- Increment heartbeat counter. Called at every operation entry point
    (eval, whnfCoreVal, forceThunk, lazyDelta step, infer, isDefEq)
    to bound total work. -/
@[inline] def heartbeat : TypecheckM σ m Unit := do
  let stt ← get
  if stt.stats.heartbeats >= stt.maxHeartbeats then
    -- Save stats snapshot before throwing (survives ExceptT unwinding)
    if let some ref := (← read).statsSnapshot then
      ref.set stt.stats
    throw s!"heartbeat limit exceeded ({stt.maxHeartbeats})"
  let hb := stt.stats.heartbeats + 1
  if (← read).trace && hb % 100_000 == 0 then
    let thunkTableSize ← do
      let table ← ST.Ref.get (← read).thunkTable
      pure table.size
    dbg_trace s!"    [hb] {hb / 1000}K heartbeats, delta={stt.stats.deltaSteps}, thunkTable={thunkTableSize}, isDefEq={stt.stats.isDefEqCalls}, eval={stt.stats.evalCalls}, force={stt.stats.forceCalls}"
  modify fun s => { s with stats.heartbeats := hb }

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
  match (← get).typedConsts.get? id with
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
  if (← get).typedConsts.get? id |>.isSome then return ()
  let ci ← derefConst id
  let tc := provisionalTypedConst ci
  modify fun stt => { stt with
    typedConsts := stt.typedConsts.insert id tc }

/-! ## Top-level runner -/

/-- Run a TypecheckM computation purely via runST + ExceptT.run.
    Everything runs inside a single ST σ region: ref creation, then the action. -/
def TypecheckM.runPure (ctx_no_thunks : ∀ σ, ST.Ref σ (Array (ST.Ref σ (ThunkEntry m))) → TypecheckCtx σ m)
    (stt : TypecheckState m)
    (action : ∀ σ, TypecheckM σ m α)
    : Except String (α × TypecheckState m) :=
  runST fun σ => do
    let thunkTable ← ST.mkRef (#[] : Array (ST.Ref σ (ThunkEntry m)))
    let ctx := ctx_no_thunks σ thunkTable
    ExceptT.run (StateT.run (ReaderT.run (action σ) ctx) stt)

/-- Simplified runner for common case. -/
def TypecheckM.runSimple (kenv : KEnv m) (prims : KPrimitives m)
    (stt : TypecheckState m := {})
    (safety : KDefinitionSafety := .safe) (quotInit : Bool := false)
    (action : ∀ σ, TypecheckM σ m α)
    : Except String (α × TypecheckState m) :=
  TypecheckM.runPure
    (fun _σ thunkTable => {
      types := #[], letValues := #[], kenv, prims, safety, quotInit,
      thunkTable })
    stt action

end Ix.Kernel
