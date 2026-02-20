/-
  TypecheckM: Monad stack, context, state, and utilities for the kernel typechecker.
-/
import Ix.Kernel.Datatypes
import Ix.Kernel.Level

namespace Ix.Kernel

/-! ## Typechecker Context -/

structure TypecheckCtx (m : MetaMode) where
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
  depth    : Nat := 3000
  /-- Enable dbg_trace on major entry points for debugging. -/
  trace    : Bool := false
  deriving Inhabited

/-! ## Typechecker State -/

/-- Default fuel for bounding total recursive work per constant. -/
def defaultFuel : Nat := 100000

structure TypecheckState (m : MetaMode) where
  typedConsts : Std.TreeMap Address (TypedConst m) Address.compare
  /-- Fuel counter for bounding total recursive work. Decremented on each entry to
      eval/equal/infer. Reset at the start of each `checkConst` call. -/
  fuel : Nat := defaultFuel
  /-- Cache for evaluated constant definitions. Maps an address to its universe
      parameters and evaluated value. Universe-polymorphic constants produce different
      values for different universe instantiations, so we store and check univs. -/
  evalCache : Std.HashMap Address (Array (Level m) × Value m) := {}
  /-- Cache for definitional equality results. Maps `(ptrAddrUnsafe a, ptrAddrUnsafe b)`
      (canonicalized so smaller pointer comes first) to `Bool`. Only `true` results are
      cached (monotone under state growth). -/
  equalCache : Std.HashMap (USize × USize) Bool := {}
  /-- Cache for constant type SusValues. When `infer (.const addr _)` computes a
      suspended type, it is cached here so repeated references to the same constant
      share the same SusValue pointer, enabling fast-path pointer equality in `equal`.
      Stores universe parameters alongside the value for correctness with polymorphic constants. -/
  constTypeCache : Std.HashMap Address (List (Level m) × SusValue m) := {}
  deriving Inhabited

/-! ## TypecheckM monad -/

abbrev TypecheckM (m : MetaMode) := ReaderT (TypecheckCtx m) (StateT (TypecheckState m) (Except String))

def TypecheckM.run (ctx : TypecheckCtx m) (stt : TypecheckState m) (x : TypecheckM m α) : Except String α :=
  match (StateT.run (ReaderT.run x ctx) stt) with
  | .error e => .error e
  | .ok (a, _) => .ok a

def TypecheckM.runState (ctx : TypecheckCtx m) (stt : TypecheckState m) (x : TypecheckM m α)
    : Except String (α × TypecheckState m) :=
  StateT.run (ReaderT.run x ctx) stt

/-! ## Context modifiers -/

def withEnv (env : ValEnv m) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with env := env }

def withResetCtx : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with
    lvl := 0, env := default, types := default, mutTypes := default, recAddr? := none }

def withMutTypes (mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → SusValue m)) compare) :
    TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

def withExtendedCtx (val typ : SusValue m) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    types := typ :: ctx.types,
    env := ctx.env.extendWith val }

def withExtendedEnv (thunk : SusValue m) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with env := ctx.env.extendWith thunk }

def withNewExtendedEnv (env : ValEnv m) (thunk : SusValue m) :
    TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with env := env.extendWith thunk }

def withRecAddr (addr : Address) : TypecheckM m α → TypecheckM m α :=
  withReader fun ctx => { ctx with recAddr? := some addr }

/-- Check both fuel counters, decrement them, and run the action.
    - State fuel bounds total work (prevents exponential blowup / hanging).
    - Reader depth bounds call-stack depth (prevents native stack overflow). -/
def withFuelCheck (action : TypecheckM m α) : TypecheckM m α := do
  let ctx ← read
  if ctx.depth == 0 then
    throw "deep recursion depth limit reached"
  let stt ← get
  if stt.fuel == 0 then throw "deep recursion work limit reached"
  set { stt with fuel := stt.fuel - 1 }
  withReader (fun ctx => { ctx with depth := ctx.depth - 1 }) action

/-! ## Name lookup -/

/-- Look up the MetaField name for a constant address from the kernel environment. -/
def lookupName (addr : Address) : TypecheckM m (MetaField m Ix.Name) := do
  match (← read).kenv.find? addr with
  | some ci => pure ci.cv.name
  | none => pure default

/-! ## Const dereferencing -/

def derefConst (addr : Address) : TypecheckM m (ConstantInfo m) := do
  let ctx ← read
  match ctx.kenv.find? addr with
  | some ci => pure ci
  | none => throw s!"unknown constant {addr}"

def derefTypedConst (addr : Address) : TypecheckM m (TypedConst m) := do
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
def ensureTypedConst (addr : Address) : TypecheckM m Unit := do
  if (← get).typedConsts.get? addr |>.isSome then return ()
  let ci ← derefConst addr
  let tc := provisionalTypedConst ci
  modify fun stt => { stt with
    typedConsts := stt.typedConsts.insert addr tc }

end Ix.Kernel
