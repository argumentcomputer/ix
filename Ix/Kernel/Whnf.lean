/-
  Kernel Whnf: Environment-based weak head normal form reduction.

  Works directly on `Expr m` with deferred substitution via closures.
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

open Level (instBulkReduce reduceIMax)

/-! ## Helpers -/

/-- Check if an address is a primitive operation that takes arguments. -/
def isPrimOp (prims : Primitives) (addr : Address) : Bool :=
  addr == prims.natAdd || addr == prims.natSub || addr == prims.natMul ||
  addr == prims.natPow || addr == prims.natGcd || addr == prims.natMod ||
  addr == prims.natDiv || addr == prims.natBeq || addr == prims.natBle ||
  addr == prims.natLand || addr == prims.natLor || addr == prims.natXor ||
  addr == prims.natShiftLeft || addr == prims.natShiftRight ||
  addr == prims.natSucc

/-- Look up element in a list by index. -/
def listGet? (l : List α) (n : Nat) : Option α :=
  match l, n with
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n+1 => listGet? l n

/-! ## Nat primitive reduction on Expr -/

/-- Extract a Nat value from an expression, handling both literal and constructor forms.
    Matches lean4lean's `rawNatLitExt?` and lean4 C++'s `is_nat_lit_ext`. -/
def extractNatVal (prims : Primitives) (e : Expr m) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .const addr _ _ => if addr == prims.natZero then some 0 else none
  | _ => none

/-- Try to reduce a Nat primitive applied to literal arguments (no whnf on args).
    Used in lazyDeltaReduction where args are already partially reduced. -/
def tryReduceNatLit (e : Expr m) : TypecheckM m (Option (Expr m)) := do
  let fn := e.getAppFn
  match fn with
  | .const addr _ _ =>
    let prims := (← read).prims
    if !isPrimOp prims addr then return none
    let args := e.getAppArgs
    -- Nat.succ: 1 arg
    if addr == prims.natSucc then
      if args.size >= 1 then
        match extractNatVal prims args[0]! with
        | some n => return some (.lit (.natVal (n + 1)))
        | none => return none
      else return none
    -- Binary nat operations: 2 args
    else if args.size >= 2 then
      match extractNatVal prims args[0]!, extractNatVal prims args[1]! with
      | some x, some y =>
        if addr == prims.natAdd then return some (.lit (.natVal (x + y)))
        else if addr == prims.natSub then return some (.lit (.natVal (x - y)))
        else if addr == prims.natMul then return some (.lit (.natVal (x * y)))
        else if addr == prims.natPow then
          if y > 16777216 then return none
          return some (.lit (.natVal (Nat.pow x y)))
        else if addr == prims.natMod then return some (.lit (.natVal (x % y)))
        else if addr == prims.natDiv then return some (.lit (.natVal (x / y)))
        else if addr == prims.natGcd then return some (.lit (.natVal (Nat.gcd x y)))
        else if addr == prims.natBeq then
          let boolAddr := if x == y then prims.boolTrue else prims.boolFalse
          return some (Expr.mkConst boolAddr #[])
        else if addr == prims.natBle then
          let boolAddr := if x ≤ y then prims.boolTrue else prims.boolFalse
          return some (Expr.mkConst boolAddr #[])
        else if addr == prims.natLand then return some (.lit (.natVal (Nat.land x y)))
        else if addr == prims.natLor then return some (.lit (.natVal (Nat.lor x y)))
        else if addr == prims.natXor then return some (.lit (.natVal (Nat.xor x y)))
        else if addr == prims.natShiftLeft then return some (.lit (.natVal (Nat.shiftLeft x y)))
        else if addr == prims.natShiftRight then return some (.lit (.natVal (Nat.shiftRight x y)))
        else return none
      | _, _ => return none
    else return none
  | _ => return none

/-- Convert a nat literal to Nat.succ/Nat.zero constructor expressions. -/
def toCtorIfLit (prims : Primitives) : Expr m → Expr m
  | .lit (.natVal 0) => Expr.mkConst prims.natZero #[]
  | .lit (.natVal (n+1)) =>
    Expr.mkApp (Expr.mkConst prims.natSucc #[]) (.lit (.natVal n))
  | e => e

/-- Expand a string literal to its constructor form: String.mk (list-of-chars). -/
def strLitToConstructor (prims : Primitives) (s : String) : Expr m :=
  let mkCharOfNat (c : Char) : Expr m :=
    Expr.mkApp (Expr.mkConst prims.charMk #[]) (.lit (.natVal c.toNat))
  let charType : Expr m := Expr.mkConst prims.char #[]
  let nilVal : Expr m :=
    Expr.mkApp (Expr.mkConst prims.listNil #[.zero]) charType
  let listVal := s.toList.foldr (fun c acc =>
    let head := mkCharOfNat c
    Expr.mkApp (Expr.mkApp (Expr.mkApp (Expr.mkConst prims.listCons #[.zero]) charType) head) acc
  ) nilVal
  Expr.mkApp (Expr.mkConst prims.stringMk #[]) listVal

/-! ## WHNF core (structural reduction) -/

/-- Reduce a projection if the struct is a constructor application. -/
partial def reduceProj (typeAddr : Address) (idx : Nat) (struct : Expr m) : TypecheckM m (Option (Expr m)) := do
  -- Expand string literals to constructor form before projecting
  let prims := (← read).prims
  let struct' := match struct with
    | .lit (.strVal s) => strLitToConstructor prims s
    | e => e
  let fn := struct'.getAppFn
  match fn with
  | .const ctorAddr _ _ => do
    match (← read).kenv.find? ctorAddr with
    | some (.ctorInfo v) =>
      let args := struct'.getAppArgs
      let realIdx := v.numParams + idx
      if h : realIdx < args.size then
        return some args[realIdx]
      else
        return none
    | _ => return none
  | _ => return none

-- NOTE: The whnf mutual block has been moved to Infer.lean to enable
-- whnf functions to call infer/isDefEq (needed for toCtorWhenK, isProp checks).
-- Non-mutual helpers (reduceProj, toCtorIfLit, etc.) remain here.

/-! ## Literal folding for pretty printing -/

/-- Try to extract a Char from a Char.ofNat application in an Expr. -/
private partial def tryFoldChar (prims : Primitives) (e : Expr m) : Option Char :=
  match e.getAppFn with
  | .const addr _ _ =>
    if addr == prims.charMk then
      let args := e.getAppArgs
      if args.size == 1 then
        match args[0]! with
        | .lit (.natVal n) => some (Char.ofNat n)
        | _ => none
      else none
    else none
  | _ => none

/-- Try to extract a List Char from a List.cons/List.nil chain in an Expr. -/
private partial def tryFoldCharList (prims : Primitives) (e : Expr m) : Option (List Char) :=
  match e.getAppFn with
  | .const addr _ _ =>
    if addr == prims.listNil then some []
    else if addr == prims.listCons then
      let args := e.getAppArgs
      if args.size == 3 then
        match tryFoldChar prims args[1]!, tryFoldCharList prims args[2]! with
        | some c, some cs => some (c :: cs)
        | _, _ => none
      else none
    else none
  | _ => none

/-- Walk an Expr and fold Nat.zero/Nat.succ chains to nat literals,
    and String.mk (char list) to string literals. -/
partial def foldLiterals (prims : Primitives) : Expr m → Expr m
  | .const addr lvls name =>
    if addr == prims.natZero then .lit (.natVal 0)
    else .const addr lvls name
  | .app fn arg =>
    let fn' := foldLiterals prims fn
    let arg' := foldLiterals prims arg
    let e := Expr.app fn' arg'
    match e.getAppFn with
    | .const addr _ _ =>
      if addr == prims.natSucc && e.getAppNumArgs == 1 then
        match e.appArg! with
        | .lit (.natVal n) => .lit (.natVal (n + 1))
        | _ => e
      else if addr == prims.stringMk && e.getAppNumArgs == 1 then
        match tryFoldCharList prims e.appArg! with
        | some cs => .lit (.strVal (String.ofList cs))
        | none => e
      else e
    | _ => e
  | .lam ty body n bi =>
    .lam (foldLiterals prims ty) (foldLiterals prims body) n bi
  | .forallE ty body n bi =>
    .forallE (foldLiterals prims ty) (foldLiterals prims body) n bi
  | .letE ty val body n =>
    .letE (foldLiterals prims ty) (foldLiterals prims val) (foldLiterals prims body) n
  | .proj ta idx s tn =>
    .proj ta idx (foldLiterals prims s) tn
  | e => e

/-! ## isDelta helper -/

/-- Check if an expression's head is a delta-reducible constant.
    Returns the DefinitionVal if so. -/
def isDelta (e : Expr m) (kenv : Env m) : Option (ConstantInfo m) :=
  match e.getAppFn with
  | .const addr _ _ =>
    match kenv.find? addr with
    | some ci@(.defnInfo _) => some ci
    | some ci@(.thmInfo _) => some ci
    | _ => none
  | _ => none

end Ix.Kernel
