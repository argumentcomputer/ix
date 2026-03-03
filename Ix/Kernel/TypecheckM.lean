/-
  TypecheckM: Monad stack, context, state, and utilities for the kernel typechecker.

  Environment-based kernel: no ST, no thunks, no Value domain.
  Types and values are Expr m throughout.
-/
import Ix.Kernel.Datatypes
import Ix.Kernel.Level
import Ix.Kernel.EquivManager

namespace Ix.Kernel

/-! ## Level substitution on Expr -/

/-- Substitute universe level params in an expression using `instBulkReduce`. -/
def Expr.instantiateLevelParams (e : Expr m) (levels : Array (Level m)) : Expr m :=
  if levels.isEmpty then e
  else e.instantiateLevelParamsBy (Level.instBulkReduce levels)

/-! ## Typechecker Context -/

structure TypecheckCtx (m : MetaMode) where
  /-- Type of each bound variable, indexed by de Bruijn index.
      types[0] is the type of bvar 0 (most recently bound). -/
  types    : Array (Expr m)
  kenv     : Env m
  prims    : Primitives
  safety   : DefinitionSafety
  quotInit : Bool
  /-- Maps a variable index (mutual reference) to (address, type function). -/
  mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → Expr m)) compare
  /-- Tracks the address of the constant currently being checked, for recursion detection. -/
  recAddr? : Option Address
  /-- When true, skip argument type-checking during inference (lean4lean inferOnly). -/
  inferOnly : Bool := false
  /-- Enable dbg_trace on major entry points for debugging. -/
  trace    : Bool := false

/-! ## Typechecker State -/

/-- Default fuel for bounding total recursive work per constant. -/
def defaultFuel : Nat := 10_000_000

structure TypecheckState (m : MetaMode) where
  typedConsts    : Std.TreeMap Address (TypedConst m) Address.compare
  whnfCache      : Std.TreeMap (Expr m) (Expr m) Expr.compare := {}
  /-- Cache for structural-only WHNF (whnfCore with cheapRec=false, cheapProj=false).
      Separate from whnfCache to avoid stale entries from cheap reductions. -/
  whnfCoreCache  : Std.TreeMap (Expr m) (Expr m) Expr.compare := {}
  /-- Infer cache: maps term → (binding context, inferred type).
      Keyed on Expr only; context verified on retrieval via ptr equality + BEq fallback. -/
  inferCache     : Std.TreeMap (Expr m) (Array (Expr m) × Expr m) Expr.compare := {}
  eqvManager     : EquivManager m := {}
  failureCache   : Std.TreeMap (Expr m × Expr m) Unit Expr.pairCompare := {}
  constTypeCache : Std.TreeMap Address (Array (Level m) × Expr m) Address.compare := {}
  fuel           : Nat := defaultFuel
  /-- Tracks nesting depth of whnf calls from within recursor reduction (tryReduceApp → whnf).
      When this exceeds a threshold, whnfCore is used instead of whnf to prevent stack overflow. -/
  whnfDepth      : Nat := 0
  /-- Global recursion depth across isDefEq/infer/whnf for stack overflow prevention. -/
  recDepth       : Nat := 0
  maxRecDepth    : Nat := 0
  deriving Inhabited

/-! ## TypecheckM monad -/

abbrev TypecheckM (m : MetaMode) :=
  ReaderT (TypecheckCtx m) (ExceptT String (StateM (TypecheckState m)))

def TypecheckM.run (ctx : TypecheckCtx m) (stt : TypecheckState m)
    (x : TypecheckM m α) : Except String α × TypecheckState m :=
  let (result, stt') := StateT.run (ExceptT.run (ReaderT.run x ctx)) stt
  (result, stt')

/-! ## Context modifiers -/

def withResetCtx : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with
    types := #[], mutTypes := default, recAddr? := none }

def withMutTypes (mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → Expr m)) compare) :
    TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

/-- Extend the context with a new bound variable of the given type. -/
def withExtendedCtx (varType : Expr m) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with types := ctx.types.push varType }

def withRecAddr (addr : Address) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with recAddr? := some addr }

def withInferOnly : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with inferOnly := true }

/-- The current binding depth (number of bound variables in scope). -/
def lvl : TypecheckM m Nat := do pure (← read).types.size

/-- Check fuel and decrement it. -/
def withFuelCheck (action : TypecheckM m α) : TypecheckM m α := do
  let stt ← get
  if stt.fuel == 0 then throw "deep recursion fuel limit reached"
  modify fun s => { s with fuel := s.fuel - 1 }
  action

/-! ## Name lookup -/

/-- Look up the MetaField name for a constant address from the kernel environment. -/
def lookupName (addr : Address) : TypecheckM m (MetaField m Ix.Name) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci.cv.name
  | none => pure default

/-! ## Const dereferencing -/

def derefConst (addr : Address) : TypecheckM m (ConstantInfo m) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci
  | none => throw s!"unknown constant {addr}"

def derefTypedConst (addr : Address) : TypecheckM m (TypedConst m) := do
  match (← get).typedConsts.get? addr with
  | some tc => pure tc
  | none => throw s!"typed constant not found: {addr}"

/-! ## Provisional TypedConst -/

/-- Extract the major premise's inductive address from a recursor type. -/
def getMajorInduct (type : Expr m) (numParams numMotives numMinors numIndices : Nat) : Option Address :=
  go (numParams + numMotives + numMinors + numIndices) type
where
  go : Nat → Expr m → Option Address
    | 0, e => match e with
      | .forallE dom _ _ _ => some dom.getAppFn.constAddr!
      | _ => none
    | n+1, e => match e with
      | .forallE _ body _ _ => go n body
      | _ => none

/-- Build a provisional TypedConst entry from raw ConstantInfo. -/
def provisionalTypedConst (ci : ConstantInfo m) : TypedConst m :=
  let rawType : TypedExpr m := ⟨default, ci.type⟩
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
    let typedRules := v.rules.map fun r => (r.nfields, (⟨default, r.rhs⟩ : TypedExpr m))
    .recursor rawType v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules

/-- Ensure a constant has a TypedConst entry. -/
def ensureTypedConst (addr : Address) : TypecheckM m Unit := do
  if (← get).typedConsts.get? addr |>.isSome then return ()
  let ci ← derefConst addr
  let tc := provisionalTypedConst ci
  modify fun stt => { stt with
    typedConsts := stt.typedConsts.insert addr tc }

/-! ## Def-eq cache helpers -/

/-- Symmetric cache key for def-eq pairs. Orders by pointer address to make key(a,b) == key(b,a). -/
def eqCacheKey (a b : Expr m) : Expr m × Expr m :=
  if Expr.ptrCompare a b != .gt then (a, b) else (b, a)

end Ix.Kernel
