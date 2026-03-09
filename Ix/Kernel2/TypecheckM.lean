/-
  Kernel2 TypecheckM: Monad stack, context, state, and thunk operations.

  Monad is based on EST (ExceptT + ST) for pure mutable references.
  σ parameterizes the ST region — runEST at the top level keeps everything pure.
  Context stores types as Val (indexed by de Bruijn level, not index).
  Thunk table lives in the reader context (ST.Ref identity doesn't change).
-/
import Ix.Kernel2.Value
import Ix.Kernel2.EquivManager
import Ix.Kernel.Datatypes
import Ix.Kernel.Level
import Init.System.ST

namespace Ix.Kernel2

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

/-! ## Typechecker Context -/

structure TypecheckCtx (σ : Type) (m : Ix.Kernel.MetaMode) where
  types      : Array (Val m)
  letValues  : Array (Option (Val m)) := #[]
  binderNames : Array (KMetaField m Ix.Name) := #[]
  kenv       : KEnv m
  prims      : KPrimitives
  safety     : KDefinitionSafety
  quotInit   : Bool
  mutTypes   : Std.TreeMap Nat (Address × (Array (KLevel m) → Val m)) compare := default
  recAddr?   : Option Address := none
  inferOnly  : Bool := false
  eagerReduce : Bool := false
  trace      : Bool := false
  -- Thunk table: ST.Ref to array of ST.Ref thunk entries
  thunkTable : ST.Ref σ (Array (ST.Ref σ (ThunkEntry m)))

/-! ## Typechecker State -/

def defaultFuel : Nat := 10_000_000

private def ptrPairOrd : Ord (USize × USize) where
  compare a b :=
    match compare a.1 b.1 with
    | .eq => compare a.2 b.2
    | r => r

structure TypecheckState (m : Ix.Kernel.MetaMode) where
  typedConsts    : Std.TreeMap Address (KTypedConst m) Ix.Kernel.Address.compare := default
  failureCache   : Std.TreeMap (KExpr m × KExpr m) Unit Ix.Kernel.Expr.pairCompare := default
  ptrFailureCache : Std.TreeMap (USize × USize) (Val m × Val m) ptrPairOrd.compare := default
  ptrSuccessCache : Std.TreeMap (USize × USize) (Val m × Val m) ptrPairOrd.compare := default
  eqvManager     : EquivManager := {}
  keepAlive      : Array (Val m) := #[]
  inferCache     : Std.TreeMap (KExpr m) (Array (Val m) × KTypedExpr m × Val m)
                     Ix.Kernel.Expr.compare := default
  whnfCache      : Std.TreeMap USize (Val m × Val m) compare := default
  fuel           : Nat := defaultFuel
  recDepth       : Nat := 0
  maxRecDepth    : Nat := 0
  inferCalls     : Nat := 0
  evalCalls      : Nat := 0
  forceCalls     : Nat := 0
  isDefEqCalls   : Nat := 0
  thunkCount     : Nat := 0
  thunkForces    : Nat := 0
  thunkHits      : Nat := 0
  cacheHits      : Nat := 0
  deriving Inhabited

/-! ## TypecheckM monad

  ReaderT for immutable context (including thunk table ref).
  StateT for mutable counters/caches (typedConsts, fuel, etc.).
  ExceptT for errors, ST for mutable thunk refs. -/

abbrev TypecheckM (σ : Type) (m : Ix.Kernel.MetaMode) :=
  ReaderT (TypecheckCtx σ m) (StateT (TypecheckState m) (ExceptT String (ST σ)))

/-! ## Thunk operations -/

/-- Allocate a new thunk (unevaluated). Returns its Nat. -/
def mkThunk (expr : KExpr m) (env : Array (Val m)) : TypecheckM σ m Nat := do
  let tableRef := (← read).thunkTable
  let table ← tableRef.get
  let entryRef ← ST.mkRef (ThunkEntry.unevaluated expr env)
  tableRef.set (table.push entryRef)
  let id := table.size
  modify fun s => { s with thunkCount := s.thunkCount + 1 }
  pure id

/-- Allocate a thunk that is already evaluated. -/
def mkThunkFromVal (v : Val m) : TypecheckM σ m Nat := do
  let tableRef := (← read).thunkTable
  let table ← tableRef.get
  let entryRef ← ST.mkRef (ThunkEntry.evaluated v)
  tableRef.set (table.push entryRef)
  let id := table.size
  modify fun s => { s with thunkCount := s.thunkCount + 1 }
  pure id

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
    mutTypes := default, recAddr? := none }

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

def withMutTypes (mutTypes : Std.TreeMap Nat (Address × (Array (KLevel m) → Val m)) compare) :
    TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

def withRecAddr (addr : Address) : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with recAddr? := some addr }

def withInferOnly : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with inferOnly := true }

def withSafety (s : KDefinitionSafety) : TypecheckM σ m α → TypecheckM σ m α :=
  withReader fun ctx => { ctx with safety := s }

def mkFreshFVar (ty : Val m) : TypecheckM σ m (Val m) := do
  let d ← depth
  pure (Val.mkFVar d ty)

/-! ## Fuel and recursion depth -/

def withFuelCheck (action : TypecheckM σ m α) : TypecheckM σ m α := do
  let stt ← get
  if stt.fuel == 0 then throw "fuel limit reached"
  modify fun s => { s with fuel := s.fuel - 1 }
  action

def maxRecursionDepth : Nat := 2000

def withRecDepthCheck (action : TypecheckM σ m α) : TypecheckM σ m α := do
  let d := (← get).recDepth
  if d >= maxRecursionDepth then
    throw s!"maximum recursion depth ({maxRecursionDepth}) exceeded"
  modify fun s => { s with recDepth := d + 1, maxRecDepth := max s.maxRecDepth (d + 1) }
  let r ← action
  modify fun s => { s with recDepth := d }
  pure r

/-! ## Const dereferencing -/

def derefConst (addr : Address) : TypecheckM σ m (KConstantInfo m) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci
  | none => throw s!"unknown constant {addr}"

def derefTypedConst (addr : Address) : TypecheckM σ m (KTypedConst m) := do
  match (← get).typedConsts.get? addr with
  | some tc => pure tc
  | none => throw s!"typed constant not found: {addr}"

def lookupName (addr : Address) : TypecheckM σ m (KMetaField m Ix.Name) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci.cv.name
  | none => pure default

/-! ## Provisional TypedConst -/

def getMajorInduct (type : KExpr m) (numParams numMotives numMinors numIndices : Nat)
    : Option Address :=
  go (numParams + numMotives + numMinors + numIndices) type
where
  go : Nat → KExpr m → Option Address
    | 0, e => match e with
      | .forallE dom _ _ _ => some dom.getAppFn.constAddr!
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
    let indAddr := getMajorInduct ci.type v.numParams v.numMotives v.numMinors v.numIndices
      |>.getD default
    let typedRules := v.rules.map fun r => (r.nfields, (⟨default, r.rhs⟩ : KTypedExpr m))
    .recursor rawType v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules

def ensureTypedConst (addr : Address) : TypecheckM σ m Unit := do
  if (← get).typedConsts.get? addr |>.isSome then return ()
  let ci ← derefConst addr
  let tc := provisionalTypedConst ci
  modify fun stt => { stt with
    typedConsts := stt.typedConsts.insert addr tc }

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
def TypecheckM.runSimple (kenv : KEnv m) (prims : KPrimitives)
    (stt : TypecheckState m := {})
    (safety : KDefinitionSafety := .safe) (quotInit : Bool := false)
    (action : ∀ σ, TypecheckM σ m α)
    : Except String (α × TypecheckState m) :=
  TypecheckM.runPure
    (fun _σ thunkTable => {
      types := #[], letValues := #[], kenv, prims, safety, quotInit,
      thunkTable })
    stt action

end Ix.Kernel2
