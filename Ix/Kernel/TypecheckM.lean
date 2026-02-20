/-
  TypecheckM: Monad stack, context, state, and utilities for the kernel typechecker.
-/
import Ix.Kernel.Datatypes
import Ix.Kernel.Level

namespace Ix.Kernel

/-! ## Typechecker Context -/

structure TypecheckCtx (m : MetaMode) (σ : Type) where
  lvl      : Nat
  env      : ValEnv m
  types    : List (SusValue m)
  kenv     : Env m
  prims    : Primitives
  safety   : DefinitionSafety
  quotInit : Bool
  /-- Maps a variable index (mutual reference) to (address, type-value function). -/
  mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → SusValue m)) compare
  /-- Tracks the address of the constant currently being checked, for recursion detection. -/
  recAddr? : Option Address
  /-- Depth fuel: bounds the call-stack depth to prevent native stack overflow.
      Decremented via the reader on each entry to eval/equal/infer.
      Thunks inherit the depth from their capture point. -/
  depth    : Nat := 10000
  /-- Enable dbg_trace on major entry points for debugging. -/
  trace    : Bool := false
  /-- Global fuel counter: bounds total recursive work across all thunks via ST.Ref. -/
  fuelRef       : ST.Ref σ Nat
  /-- Mutable eval cache: persists across thunk evaluations via ST.Ref. -/
  evalCacheRef  : ST.Ref σ (Std.HashMap Address (Array (Level m) × Value m))
  /-- Mutable equality cache: persists across thunk evaluations via ST.Ref. -/
  equalCacheRef : ST.Ref σ (Std.HashMap (USize × USize) Bool)

/-! ## Typechecker State -/

/-- Default fuel for bounding total recursive work per constant. -/
def defaultFuel : Nat := 200000

structure TypecheckState (m : MetaMode) where
  typedConsts : Std.TreeMap Address (TypedConst m) Address.compare
  /-- Cache for constant type SusValues. When `infer (.const addr _)` computes a
      suspended type, it is cached here so repeated references to the same constant
      share the same SusValue pointer, enabling fast-path pointer equality in `equal`.
      Stores universe parameters alongside the value for correctness with polymorphic constants. -/
  constTypeCache : Std.HashMap Address (List (Level m) × SusValue m) := {}
  deriving Inhabited

/-! ## TypecheckM monad -/

abbrev TypecheckM (m : MetaMode) (σ : Type) :=
  ReaderT (TypecheckCtx m σ) (ExceptT String (StateT (TypecheckState m) (ST σ)))

def TypecheckM.run (ctx : TypecheckCtx m σ) (stt : TypecheckState m)
    (x : TypecheckM m σ α) : ST σ (Except String α) := do
  let (result, _) ← StateT.run (ExceptT.run (ReaderT.run x ctx)) stt
  pure result

def TypecheckM.runState (ctx : TypecheckCtx m σ) (stt : TypecheckState m) (x : TypecheckM m σ α)
    : ST σ (Except String (α × TypecheckState m)) := do
  let (result, stt') ← StateT.run (ExceptT.run (ReaderT.run x ctx)) stt
  pure (match result with | .ok a => .ok (a, stt') | .error e => .error e)

/-! ## pureRunST -/

/-- Unsafe bridge: run ST σ from pure code (for Thunk bodies).
    Safe because the only side effects are append-only cache mutations. -/
@[inline] unsafe def pureRunSTImpl {σ α : Type} [Inhabited α] (x : ST σ α) : α :=
  (x (unsafeCast ())).val

@[implemented_by pureRunSTImpl]
opaque pureRunST {σ α : Type} [Inhabited α] : ST σ α → α

/-! ## Context modifiers -/

def withEnv (env : ValEnv m) : TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with env := env }

def withResetCtx : TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with
    lvl := 0, env := default, types := default, mutTypes := default, recAddr? := none }

def withMutTypes (mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → SusValue m)) compare) :
    TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

def withExtendedCtx (val typ : SusValue m) : TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    types := typ :: ctx.types,
    env := ctx.env.extendWith val }

def withExtendedEnv (thunk : SusValue m) : TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with env := ctx.env.extendWith thunk }

def withNewExtendedEnv (env : ValEnv m) (thunk : SusValue m) :
    TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with env := env.extendWith thunk }

def withRecAddr (addr : Address) : TypecheckM m σ α → TypecheckM m σ α :=
  withReader fun ctx => { ctx with recAddr? := some addr }

/-- Check both fuel counters, decrement them, and run the action.
    - State fuel bounds total work (prevents exponential blowup / hanging).
    - Reader depth bounds call-stack depth (prevents native stack overflow). -/
def withFuelCheck (action : TypecheckM m σ α) : TypecheckM m σ α := do
  let ctx ← read
  if ctx.depth == 0 then
    throw "deep recursion depth limit reached"
  let fuel ← ctx.fuelRef.get
  if fuel == 0 then throw "deep recursion fuel limit reached"
  let _ ← ctx.fuelRef.set (fuel - 1)
  withReader (fun ctx => { ctx with depth := ctx.depth - 1 }) action

/-! ## Name lookup -/

/-- Look up the MetaField name for a constant address from the kernel environment. -/
def lookupName (addr : Address) : TypecheckM m σ (MetaField m Ix.Name) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci.cv.name
  | none => pure default

/-! ## Const dereferencing -/

def derefConst (addr : Address) : TypecheckM m σ (ConstantInfo m) := do
  let ctx ← read
  match ctx.kenv.find? addr with
  | some ci => pure ci
  | none => throw s!"unknown constant {addr}"

def derefTypedConst (addr : Address) : TypecheckM m σ (TypedConst m) := do
  match (← get).typedConsts.get? addr with
  | some tc => pure tc
  | none => throw s!"typed constant not found: {addr}"

/-! ## Provisional TypedConst -/

/-- Extract the major premise's inductive address from a recursor type.
    Skips numParams + numMotives + numMinors + numIndices foralls,
    then the next forall's domain's app head is the inductive const. -/
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

/-- Build a provisional TypedConst entry from raw ConstantInfo.
    Used when `infer` encounters a `.const` reference before the constant
    has been fully typechecked. The entry uses default TypeInfo and raw
    expressions directly from the kernel environment. -/
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
    let isStruct := v.ctors.size == 1  -- approximate; refined by checkIndBlock
    .inductive rawType isStruct
  | .ctorInfo v => .constructor rawType v.cidx v.numFields
  | .recInfo v =>
    let indAddr := getMajorInduct ci.type v.numParams v.numMotives v.numMinors v.numIndices
      |>.getD default
    let typedRules := v.rules.map fun r => (r.nfields, (⟨default, r.rhs⟩ : TypedExpr m))
    .recursor rawType v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules

/-- Ensure a constant has a TypedConst entry. If not already present, build a
    provisional one from raw ConstantInfo. This avoids the deep recursion of
    `checkConst` when called from `infer`. -/
def ensureTypedConst (addr : Address) : TypecheckM m σ Unit := do
  if (← get).typedConsts.get? addr |>.isSome then return ()
  let ci ← derefConst addr
  let tc := provisionalTypedConst ci
  modify fun stt => { stt with
    typedConsts := stt.typedConsts.insert addr tc }

end Ix.Kernel
