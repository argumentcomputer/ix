/-
  ExprUtils: Pure utility functions on Expr shared between kernel subsystems.

  Extracted from Kernel/Infer.lean (recursor rule helpers, inductive validation)
  and Kernel/TypecheckM.lean (level substitution).
-/
import Ix.Kernel.Level

namespace Ix.Kernel

/-! ## Level substitution on Expr -/

/-- Substitute universe level params in an expression using `instBulkReduce`. -/
def Expr.instantiateLevelParams (e : Expr m) (levels : Array (Level m)) : Expr m :=
  if levels.isEmpty then e
  else e.instantiateLevelParamsBy (Level.instBulkReduce levels)

/-! ## Expression traversal combinator -/

/-- Apply `f` to the immediate sub-expressions of `e`, tracking binder depth.
    Does not recurse — `f` is responsible for recursive calls. Handles the
    structural cases (app, lam, forallE, letE, proj); leaves (bvar, sort,
    const, lit) are returned unchanged. -/
@[inline] def Expr.mapSubexprs (e : Expr m) (f : Expr m → Nat → Expr m) (depth : Nat) : Expr m :=
  match e with
  | .app fn arg => .app (f fn depth) (f arg depth)
  | .lam ty body n bi => .lam (f ty depth) (f body (depth + 1)) n bi
  | .forallE ty body n bi => .forallE (f ty depth) (f body (depth + 1)) n bi
  | .letE ty val body n => .letE (f ty depth) (f val depth) (f body (depth + 1)) n
  | .proj ta idx s => .proj ta idx (f s depth)
  | e => e

/-! ## Recursor rule type helpers -/

/-- Shift bvar indices and level params in an expression from a constructor context
    to a recursor rule context.
    - `fieldDepth`: number of field binders above this expr in the ctor type
    - `bvarShift`: amount to shift param bvar refs (= numMotives + numMinors)
    - `levelShift`: amount to shift Level.param indices (= recLevelCount - ctorLevelCount)
    Bvar i at depth d is a param ref when i >= d + fieldDepth. -/
partial def shiftCtorToRule (e : Expr m) (fieldDepth : Nat) (bvarShift : Nat) (levelSubst : Array (Level m)) : Expr m :=
  if bvarShift == 0 && levelSubst.size == 0 then e else go e 0
where
  substLevel : Level m → Level m
    | .param i n => if h : i < levelSubst.size then levelSubst[i] else .param i n
    | .succ l => .succ (substLevel l)
    | .max a b => .max (substLevel a) (substLevel b)
    | .imax a b => .imax (substLevel a) (substLevel b)
    | l => l
  go (e : Expr m) (depth : Nat) : Expr m :=
    match e with
    | .bvar i n =>
      if i >= depth + fieldDepth then .bvar (i + bvarShift) n
      else e
    | .sort l => .sort (substLevel l)
    | .const id lvls => .const id (lvls.map substLevel)
    | e => e.mapSubexprs go depth

/-- Substitute extra nested param bvars in a constructor body expression.
    After peeling `cnp` params from the ctor type, extra param bvars occupy
    indices `fieldDepth..fieldDepth+numExtra-1` at depth 0 (they are the innermost
    free param bvars, below the shared params). Replace them with `vals` and
    shift shared param bvars down by `numExtra` to close the gap.
    - `fieldDepth`: number of field binders enclosing this expr (0 for return type)
    - `numExtra`: number of extra nested params (cnp - np)
    - `vals`: replacement values (already shifted for the rule context) -/
partial def substNestedParams (e : Expr m) (fieldDepth : Nat) (numExtra : Nat) (vals : Array (Expr m)) : Expr m :=
  if numExtra == 0 then e else go e 0
where
  go (e : Expr m) (depth : Nat) : Expr m :=
    match e with
    | .bvar i n =>
      let freeIdx := i - (depth + fieldDepth)  -- which param bvar (0 = innermost extra)
      if i < depth + fieldDepth then e  -- bound by field/local binder
      else if freeIdx < numExtra then
        -- Extra nested param: substitute with vals[freeIdx] shifted up by depth
        shiftCtorToRule vals[freeIdx]! 0 depth #[]
      else .bvar (i - numExtra) n  -- Shared param: shift down
    | e => e.mapSubexprs go depth

/-! ## Inductive validation helpers -/

/-- Check if an expression mentions a constant at the given address. -/
partial def exprMentionsConst (e : Expr m) (addr : Address) : Bool :=
  match e with
  | .const id _ => id.addr == addr
  | .app fn arg => exprMentionsConst fn addr || exprMentionsConst arg addr
  | .lam ty body _ _ => exprMentionsConst ty addr || exprMentionsConst body addr
  | .forallE ty body _ _ => exprMentionsConst ty addr || exprMentionsConst body addr
  | .letE ty val body _ => exprMentionsConst ty addr || exprMentionsConst val addr || exprMentionsConst body addr
  | .proj _ _ s => exprMentionsConst s addr
  | _ => false

/-- Walk a Pi chain past numParams + numFields binders to get the return type. -/
def getCtorReturnType (ctorType : Expr m) (numParams numFields : Nat) : Expr m :=
  go ctorType (numParams + numFields)
where
  go (ty : Expr m) (n : Nat) : Expr m :=
    match n, ty with
    | 0, e => e
    | n+1, .forallE _ body _ _ => go body n
    | _, e => e

/-- Extract result universe level from an inductive type expression. -/
def getIndResultLevel (indType : Expr m) : Option (Level m) :=
  go indType
where
  go : Expr m → Option (Level m)
  | .forallE _ body _ _ => go body
  | .sort lvl => some lvl
  | _ => none

/-- Extract the motive's return sort from a recursor type.
    Walks past numParams Pi binders, then walks the motive's domain to the final Sort. -/
def getMotiveSort (recType : Expr m) (numParams : Nat) : Option (Level m) :=
  go recType numParams
where
  go (ty : Expr m) : Nat → Option (Level m)
    | 0 => match ty with
      | .forallE motiveDom _ _ _ => walkToSort motiveDom
      | _ => none
    | n+1 => match ty with
      | .forallE _ body _ _ => go body n
      | _ => none
  walkToSort : Expr m → Option (Level m)
    | .forallE _ body _ _ => walkToSort body
    | .sort lvl => some lvl
    | _ => none

/-- Check if a level is definitively non-zero (always >= 1). -/
partial def levelIsNonZero : Level m → Bool
  | .succ _ => true
  | .zero => false
  | .param .. => false
  | .max a b => levelIsNonZero a || levelIsNonZero b
  | .imax _ b => levelIsNonZero b

/-! ## Literal folding helpers (used by PP) -/

private partial def tryFoldChar (prims : Primitives m) (e : Expr m) : Option Char :=
  match e.getAppFn with
  | .const id _ =>
    if id.addr == prims.charMk.addr then
      let args := e.getAppArgs
      if args.size == 1 then
        match args[0]! with
        | .lit (.natVal n) => some (Char.ofNat n)
        | _ => none
      else none
    else none
  | _ => none

private partial def tryFoldCharList (prims : Primitives m) (e : Expr m) : Option (List Char) :=
  match e.getAppFn with
  | .const id _ =>
    if id.addr == prims.listNil.addr then some []
    else if id.addr == prims.listCons.addr then
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
partial def foldLiterals (prims : Primitives m) : Expr m → Expr m
  | .const id lvls =>
    if id.addr == prims.natZero.addr then .lit (.natVal 0)
    else .const id lvls
  | .app fn arg =>
    let fn' := foldLiterals prims fn
    let arg' := foldLiterals prims arg
    let e := Expr.app fn' arg'
    match e.getAppFn with
    | .const id _ =>
      if id.addr == prims.natSucc.addr && e.getAppNumArgs == 1 then
        match e.appArg! with
        | .lit (.natVal n) => .lit (.natVal (n + 1))
        | _ => e
      else if id.addr == prims.stringMk.addr && e.getAppNumArgs == 1 then
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
  | .proj ta idx s =>
    .proj ta idx (foldLiterals prims s)
  | e => e

end Ix.Kernel
