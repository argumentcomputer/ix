/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Reference.Declaration
import Ix.Theory.Named.Reference.PtrEq
import Ix.Theory.Named.Reference.Level
import Ix.Theory.Named.Reference.Quot
import Ix.Theory.Named.Reference.Inductive.Reduce
import Ix.Theory.Named.Reference.Instantiate
import Ix.Theory.Named.Reference.ForEachExprV
import Ix.Theory.Named.Reference.FuelConfig

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

abbrev InferCache := ExprMap Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  success : Std.HashSet (Expr × Expr) := {}
  failure : Std.HashSet (Expr × Expr) := {}
  unfold : ExprMap Expr := {}

structure TypeChecker.Context where
  env : Environment
  lctx : LocalContext := {}
  safety : DefinitionSafety := .safe
  eagerReduce := false
  lparams : List Name := []
  fuel : FuelConfig := {}

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except Exception

def M.run (env : Environment) (safety : DefinitionSafety := .safe)
    (lctx : LocalContext := {}) (lparams : List Name := []) (fuel : FuelConfig := {})
    (x : M α) : Except Exception α :=
  x { env, safety, lctx, lparams, fuel } |>.run' {}

def M.runTermElab (m : M α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α := do
  ofExceptKernelException <| m.run (env := (← getEnv).toKernelEnv)
    (lctx := ← getLCtx) (safety := safety) (lparams := (← get).levelNames)

instance : MonadLift M Elab.Term.TermElabM := ⟨M.runTermElab⟩

def getEnv : M Environment := return (← read).env

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance : MonadLocalNameGenerator M where
  withFreshId x := do x (← mkFreshId)

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

structure Methods where
  protected isDefEqCore : Expr → Expr → M Bool
  protected whnfCore (e : Expr) (cheapProj := false) : M Expr
  protected whnf (e : Expr) : M Expr
  protected inferType (e : Expr) (inferOnly : Bool) : M Expr

abbrev RecM := ReaderT Methods M

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | bool (b : Bool)

namespace Inner

/-- Reduces `e` to its weak-head normal form. -/
def whnf (e : Expr) : RecM Expr := fun m => m.whnf e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

/-- Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not, throws an error with
`s` (the expression required to be a sort). -/
def ensureSortCore (e s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf e
  if e.isSort then return e
  throw <| .typeExpected (← getEnv) (← getLCtx) s

/-- Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not, throws an error
with `s := f a` (the application requiring `f` to be of function type). -/
def ensureForallCore (e s : Expr) : RecM Expr := do
  if e.isForall then return e
  let e ← whnf e
  if e.isForall then return e
  throw <| .funExpected (← getEnv) (← getLCtx) s

/-- Upper bound on the size in bytes of `n`'s runtime representation, mirroring the kernel's
`lean_nat_size_in_bytes`: a scalar occupies one machine word, and a bignum occupies its GMP limb
count times the limb size. -/
def natSizeInBytes (n : Nat) : Nat :=
  let bits := n.log2 + 1
  -- `n` is boxed once it no longer fits in a machine word minus its tag bit.
  if bits ≤ 63 then 8 else 8 * ((bits + 63) / 64)

/-- Rejects a `Nat` numeral whose size exceeds `natMaxSize`. `numBytes` is an upper bound on the
numeral's size, so this may be called before computing it. -/
def checkNatSize (numBytes : Nat) : RecM Unit := do
  if numBytes > (← readThe Context).fuel.natMaxSize then
    throw <| .other "the kernel refused a `Nat` numeral because its size exceeds the maximum; \
      raise the `natMaxSize` bound to allow it"

/-- `Nat.pow` and `Nat.shiftLeft` take their second argument (the exponent, resp. the shift
amount) as a machine `UInt32` in the kernel, so reject one that does not fit rather than
overflowing. -/
def checkCountArg (count : Nat) (op : String) : RecM Unit := do
  if count ≥ UInt32.size then
    throw <| .other s!"the kernel refused to evaluate `{op}` because its second argument does \
      not fit in a 32-bit unsigned integer"

/-- Bounds the numerals entering the kernel (e.g. source literals) by the same limit `reduceNat`
enforces on the ones it computes. -/
def checkLitSize (l : Literal) : RecM Unit := do
  if let .natVal n := l then checkNatSize (natSizeInBytes n)

/-- `checkNatSize`, conditionally: the size check the binary `Nat` operations that can grow a
numeral without bound run on their result. -/
def checkNatSizeIf (checkSize : Bool) (numBytes : Nat) : RecM Unit := do
  if checkSize then checkNatSize numBytes

/-- Rejects `base ^ exp` when it would exceed `natMaxSize`, without forming it: the result
occupies at most `natSizeInBytes base * exp` bytes (a `base` of `0` or `1` yields `0`/`1`), and
the bound is compared by division so the product is never formed either. -/
def checkPowSize (base exp : Nat) : RecM Unit := do
  checkCountArg exp "Nat.pow"
  if base > 1 && exp != 0 && natSizeInBytes base > (← readThe Context).fuel.natMaxSize / exp then
    throw <| .other "the kernel refused to evaluate `Nat.pow` because the result would exceed \
      the maximum numeral size; raise the `natMaxSize` bound to allow it"

/-- Rejects `v <<< shift` when it would exceed `natMaxSize`, without forming it: the result is
`v * 2 ^ shift`, which occupies about `natSizeInBytes v + shift / 8` bytes. `0 <<< _` is `0`. -/
def checkShiftLeftSize (v shift : Nat) : RecM Unit := do
  if v != 0 then
    checkCountArg shift "Nat.shiftLeft"
    checkNatSize (natSizeInBytes v + shift / 8 + 1)

/-- Checks that `l` does not contain any level parameters not found in the context `tc`. -/
def checkLevel (tc : Context) (l : Level) : Except Exception Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except Exception Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other "unknown free variable"

/-- Infers the type of `.const name ls`. -/
def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except Exception Expr := do
  let e := Expr.const name ls
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if !inferOnly then
    if info.isUnsafe && tc.safety != .unsafe then
      throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
    if let .defnInfo v := info then
      if v.safety == .partial && tc.safety == .safe then
        throw <| .other
          s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
    for l in ls do
      checkLevel tc l
  return info.instantiateTypeLevelParams ls

/-- Infers the type of expression `e`. If `inferOnly := false`, this function throws an error
whenever `e` is not typeable according to Lean's algorithmic typing judgment (barring resource
exhaustion: it may also throw `.deterministicTimeout` or `.deepRecursion` on a typeable term).
Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already
known to be well-typed. -/
def inferType (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType e inferOnly

/-- Infers the type of lambda expression `e`. -/
def inferLambda (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType d inferOnly) d
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Infers the type of for-all expression `e`. -/
def inferForall (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars us : Expr → RecM Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType d inferOnly) d
    let us := us.push t1.sortLevel!
    withLocalDecl name bi d fun fv =>
      loop (fvars.push fv) us body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!

/-- Whether `t` and `s` have already been found definitionally equal.

The pair is keyed on the order of the two hashes, so a later query finds the entry whichever way
round it presents the pair. This is a plain set of pairs rather than an equivalence-closure
structure on purpose: `isDefEq` is a sound but incomplete semi-decision procedure and so is not
transitive, and taking the transitive closure of its successes would make its result depend on the
order in which pairs were checked (lean4#14806). -/
def succeededBefore (success : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    success.contains (t, s)
  else if t.hash > s.hash then
    success.contains (s, t)
  else
    success.contains (t, s) || success.contains (s, t)

@[inherit_doc succeededBefore]
def cacheSuccess (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with success := st.success.insert k }

/-- Returns whether `t` and `s` are definitionally equal according to Lean's algorithmic
definitional equality judgment.

NOTE: This function does not do any typechecking of its own on `t` and `s`. So, when this is used as
part of a typechecking routine, it is expected that they are already well-typed (that is, that
`checkType t` and `checkType s` did not/would not throw an error). This is what justifies the
internal uses of `inferType` at its default `inferOnly := true`: on a well-typed subterm the fast
path returns the same type the checking path would have. -/
def isDefEqCore (t s : Expr) : RecM Bool := fun m => m.isDefEqCore t s

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : RecM Bool := do
  -- Syntactically equivalent expressions are definitionally equal without consulting or
  -- extending the success cache.  Besides avoiding needless work, this keeps exact checker
  -- executions compositional when an application argument has precisely the declared domain
  -- type.
  if t == s then return true
  let r ← isDefEqCore t s
  if r then
    cacheSuccess t s
  pure r

/-- Infers the type of application `e`, assuming that `e` is already well-typed. -/
def inferApp (e : Expr) : RecM Expr := do
  e.withApp fun f args =>
  let rec loop fType j i : RecM Expr :=
    if i < args.size then
      match fType with
      | .forallE _ _ body _ => loop body j (i+1)
      | _ => do
        let fType := fType.instantiateRevRange j i args
        let fType := (← ensureForallCore fType e).bindingBody!
        loop fType i (i+1)
    else
      return fType.instantiateRevRange j args.size args
  do loop (← inferType f) 0 0

/-- Infers the type of let-expression `e`. -/
def inferLet (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType type inferOnly) type
      let valType ← inferType val inferOnly
      if !(← isDefEq valType type) then
        throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type
    withLetDecl name type val fun fv =>
      loop (fvars.push fv) body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Gets the universe level of the sort that `e`'s type is defeq to, failing if `e` is not
a type. -/
def getSortLevel (e : Expr) : RecM Level := do
  let .sort u ← ensureSortCore (← inferType e) e | unreachable!
  return u

/-- Checks if `e` is a proposition, that is, if its type is a sort whose level normalizes to
zero. -/
def isProp (e : Expr) : RecM Bool := return (← getSortLevel e).isAlwaysZero

/-- Checks if `e` is definitely not a proposition, that is, if its type is a sort whose level
cannot normalize to zero under any instantiation. This is strictly stronger than `!(← isProp e)`,
which also holds for the levels that could go either way. -/
def isNeverProp (e : Expr) : RecM Bool := return (← getSortLevel e).isNeverZero

def invalidProj (e : Expr) : RecM α := do
  throw <| .invalidProj (← getEnv) (← getLCtx) e

def inferProjParams (proj : Expr) : List Expr → Expr → RecM Expr
  | [], r => pure r
  | arg :: args, r => do
    let .forallE _ _ body _ ← whnf r | invalidProj proj
    inferProjParams proj args (body.instantiate1 arg)

def inferProjFields (proj : Expr) (typeName : Name)
    (struct : Expr) (maybePropType : Bool) :
    Nat → Nat → Expr → RecM Expr
  | _, 0, r => pure r
  | fieldIdx, count + 1, r => do
    let .forallE _ dom body _ ← whnf r | invalidProj proj
    if body.hasLooseBVars && maybePropType then
      -- prop structs cannot have non-prop dependent fields
      if !(← isProp dom) then invalidProj proj
    inferProjFields proj typeName struct maybePropType (fieldIdx + 1) count
      (body.instantiate1 (.proj typeName fieldIdx struct))

/-- Infers the type of structure projection `e`. -/
def inferProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecM Expr := do
  let e := Expr.proj typeName idx struct
  let type ← whnf structType
  type.withApp fun I args => do
  let env ← getEnv
  let .const I_name I_levels := I | invalidProj e
  if typeName != I_name then invalidProj e
  let .inductInfo I_val ← env.get I_name | invalidProj e
  let [c] := I_val.ctors | invalidProj e
  unless env.isProjectionReadyStructure I_name do invalidProj e
  if args.size != I_val.numParams + I_val.numIndices then invalidProj e
  let c_info ← env.get c
  let .ctorInfo ctorInfo := c_info | invalidProj e
  unless idx < ctorInfo.numFields do invalidProj e
  let r ← inferProjParams e (args.toList.take I_val.numParams)
    (c_info.instantiateTypeLevelParams I_levels)
  let maybePropType := !(← getSortLevel type).isNeverZero
  let r ← inferProjFields e I_name struct maybePropType 0 idx r
  let .forallE _ dom _ _ ← whnf r | invalidProj e
  if maybePropType then if !(← isProp dom) then invalidProj e
  return dom

@[inherit_doc inferType]
def inferType' (e : Expr) (inferOnly : Bool) : RecM Expr := do
  if e.hasLooseBVars then
    throw <| .other
      s!"type checker does not support loose bound variables, \
         replace them with free variables before invoking it"
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC)[e]? then
    return r
  let r ← match e with
    | .lit l =>
      checkLitSize l
      if !inferOnly then
        match l with
        | .natVal _ => _ ← (← getEnv).get ``Nat
        | .strVal _ => _ ← (← getEnv).get ``Char.ofNat; _ ← (← getEnv).get ``String.ofList
      pure (mkConst l.typeName)
    | .mdata _ e => inferType' e inferOnly
    | .proj s idx e => inferProj s idx e (← inferType' e inferOnly)
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      if !inferOnly then
        checkLevel (← readThe Context) l
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls inferOnly
    | .lam .. => inferLambda e inferOnly
    | .forallE .. => inferForall e inferOnly
    | .app f a =>
      if inferOnly then
        inferApp e
      else
        let fType ← ensureForallCore (← inferType' f inferOnly) e
        let aType ← inferType' a inferOnly
        let dType := fType.bindingDomain!
        -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
        -- for some universe level `l`, so this use of `isDefEq` is valid
        let ok ← if a.isAppOfArity ``eagerReduce 2 then
          withTheReader Context (fun s => {s with eagerReduce := true}) <|
            isDefEq dType aType
        else
          isDefEq dType aType
        if !ok then throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
        pure <| fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

/-- Reduces `e` to its weak-head normal form, without unfolding definitions. This is a conservative
version of `whnf` (which does unfold definitions), to be used for efficiency purposes.

Setting `cheapProj` to `true` will cause the struct argument to be reduced "lazily" (using
`whnfCore` rather than `whnf`) when reducing struct projections, and suppresses caching of the
result. This can be a useful optimization if we're checking the definitional equality of two struct
projections of the same projection, where we might save some work by directly checking if the struct
arguments are defeq (rather than eagerly applying a projection).

The kernel has a companion `cheap_rec` flag doing the same for the major premise of a recursor, but
nothing has set it since lean4#9275 removed the old compiler, so it is omitted here. -/
def whnfCore (e : Expr) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCore e cheapProj

def reduceRecursor (e : Expr) : RecM (Option Expr) := do
  let env ← getEnv
  if env.quotInit then
    if let some r ← quotReduceRec e whnf then
      return r
  if let some r ← inductiveReduceRec env e whnf inferType isDefEq isNeverProp then
    return r
  return none

/-- Reduces the free variable `e`: to the `whnfCore` of its definition if `e` is a let variable,
and to itself if it is a lambda variable. -/
def whnfFVar (e : Expr) (cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapProj
  return e

/-- Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a constructor
application). -/
def reduceProj (idx : Nat) (struct : Expr) (cheapProj : Bool) : RecM (Option Expr) := do
  let mut c ← (if cheapProj then whnfCore struct cheapProj else whnf struct)
  if let .lit (.strVal s) := c then
    c ← whnf (.strLitToConstructor s)
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

@[inherit_doc whnfCore]
def whnfCore' (e : Expr) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache[e]? then
    return r
  let rec save r := do
    if !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapProj
  | .app .. =>
    -- beta-reduce at the head as much as possible, apply any remaining `rargs`
    -- to the resulting expression, and re-run `whnfCore`
    e.withAppRev fun f0 rargs => do
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let f ← whnfCore f0 cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecM Expr :=
        let rec cont := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if Expr.structuralEq f f0 then
      if let some r ← reduceRecursor e then
        whnfCore r cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      -- the recursive call re-decomposes `r` and reaches the `f == f0` branch above, so
      -- `reduceRecursor` is still applied; adding arguments can only enable further normalization
      -- if the head reduced to a partial recursor application
      save <|← whnfCore r cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapProj then
      save <|← whnfCore m cheapProj
    else
      save e

/-- Checks if the head of `e` is a constant that can be delta-reduced, applied to the right number
of universe levels, returning its `ConstantInfo` if so. See `ConstantInfo.deltaValue?` for which
constants qualify. -/
def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c ls := e.getAppFn then
    if let some ci := env.find? c then
      if ci.deltaValue?.isSome && ls.length == ci.numLevelParams then
        return ci
  none

def instantiateDeltaValue (ci : ConstantInfo) (ls : List Level) : Expr :=
  ci.deltaValue?.get!.instantiateLevelParams ci.levelParams ls

/-- If `e` is itself a constant that can be delta-reduced, returns its value with the constant's
level parameters instantiated. Unlike `unfoldDefinition`, this does not look through applications:
`e` must be a `.const`. -/
def unfoldDefinitionCore (e : Expr) : RecM (Option Expr) := do
  let .const _ ls := e | return none
  let env ← getEnv
  let some d := isDelta env e | return none
  unless 0 < ls.length do return some (instantiateDeltaValue d ls)
  if let some r := (← get).unfold[e]? then return some r
  let r := instantiateDeltaValue d ls
  modify fun s => { s with unfold := s.unfold.insert e r }
  return some r

/-- Unfolds the definition at the head of the application `e` (or `e` itself if it is not an
application). -/
def unfoldDefinition (e : Expr) : RecM (Option Expr) := do
  if e.isApp then
    let f0 := e.getAppFn
    let some f ← unfoldDefinitionCore f0 | return none
    let rargs := e.getAppRevArgs
    return f.mkAppRevRange 0 rargs.size rargs
  else
    unfoldDefinitionCore e

def reduceNative (_env : Environment) (e : Expr) : Except Exception (Option Expr) := do
  let .app f (.const c _) := e | return none
  if Expr.structuralEq f (.const ``reduceBool []) then
    throw <| .other s!"the named specification does not support 'reduceBool {c}' reduction"
  else if Expr.structuralEq f (.const ``reduceNat []) then
    throw <| .other s!"the named specification does not support 'reduceNat {c}' reduction"
  return none

def rawNatLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

/-- Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced to Nat literals.

`checkSize` bounds the size of the result, for the operations that can grow a numeral without
bound when iterated. Their operands are already bounded, so computing the result before checking
it is cheap.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) (checkSize := false) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  checkNatSizeIf checkSize (natSizeInBytes (f v1 v2))
  return some <| .lit <| .natVal <| f v1 v2

/-- Reduces `Nat.pow a b`. Unlike the other binary operations this bounds the result *before*
computing it, since a small exponent already denotes an unrepresentable numeral. -/
def reducePow (a b : Expr) : RecM (Option Expr) := do
  let some base := rawNatLitExt? (← whnf a) | return none
  let some exp := rawNatLitExt? (← whnf b) | return none
  checkPowSize base exp
  return some <| .lit <| .natVal <| Nat.pow base exp

/-- Reduces `Nat.shiftLeft a b`, bounding the result before computing it. -/
def reduceShiftLeft (a b : Expr) : RecM (Option Expr) := do
  let some v := rawNatLitExt? (← whnf a) | return none
  let some shift := rawNatLitExt? (← whnf b) | return none
  checkShiftLeftSize v shift
  return some <| .lit <| .natVal <| v <<< shift

/-- Reduces the application `f a b` to a boolean expression if `a` and `b` can be reduced to Nat
literals.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

/-- Reduces `e` to a literal if possible, where the unary operation `Nat.succ` and the binary
operations and predicates with an external implementation may be applied: `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.mod`, `Nat.div`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight` produce a `Nat` literal, while the predicates `Nat.beq` and
`Nat.ble` produce a `Bool` literal. -/
def reduceNat (e : Expr) : RecM (Option Expr) := do
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if Expr.structuralEq f (.const ``Nat.succ []) then
      let some v := rawNatLitExt? (← whnf e.appArg!) | return none
      checkNatSize (natSizeInBytes (v + 1))
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b (checkSize := true)
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b (checkSize := true)
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b (checkSize := true)
    if f == ``Nat.pow then return ← reducePow a b
    if f == ``Nat.gcd then return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
    if f == ``Nat.land then return ← reduceBinNatOp Nat.land a b
    if f == ``Nat.lor then return ← reduceBinNatOp Nat.lor a b
    if f == ``Nat.xor then return ← reduceBinNatOp Nat.xor a b
    if f == ``Nat.shiftLeft then return ← reduceShiftLeft a b
    if f == ``Nat.shiftRight then return ← reduceBinNatOp Nat.shiftRight a b
  return none

@[inherit_doc whnf]
def whnf' (e : Expr) : RecM Expr := do
  -- Do not cache easy cases
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
  | .mdata _ e => return ← whnf' e
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return e
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  if let some r := (← get).whnfCache[e]? then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let t ← whnfCore' t
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t ← unfoldDefinition t | return t
    loop t fuel
  let ctx ← readThe Context
  let r ← loop e <| if ctx.eagerReduce then ctx.fuel.whnfEager else ctx.fuel.whnf
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

/-- If `t` and `s` are lambda expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv => do
        isDefEqLambda tBody sBody (subst.push fv)
    else
      isDefEqLambda tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- If `t` and `s` are for-all expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv =>
        isDefEqForall tBody sBody (subst.push fv)
    else
      isDefEqForall tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- Decides definitional equality of `t` and `s` in the cases that can be settled without
reduction, returning `.undef` to defer to the calling function otherwise.

It returns `.true` if they are α-equivalent or have previously been checked for definitional
equality, and otherwise decides two sorts by level equivalence and two literals by equality,
returning `.false` where these disagree. Two lambdas or two for-alls are handed to
`isDefEqLambda`/`isDefEqForall`, which may return either. All remaining cases — including two
constants, two free variables, two applications and two projections — are deferred. -/
def quickIsDefEq (t s : Expr) : RecM LBool := do
  -- cheap structural check, plus the positive `isDefEq` cache
  if t == s || succeededBefore (← get).success t s then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv' a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

/-- Assuming that `t` and `s` have the same function heads, returns true if they are applications
with definitionally equal arguments (in which case they are defeq), and false otherwise (deferring
further defeq checking to caller). -/
def isDefEqArgs (t s : Expr) : RecM Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEq ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

/-- Assuming `t` and `s` are WHNF, checks if they are defeq on account of `t` being an η-expansion
of `s`.

Assuming that `s` has a function type `(x : A) → B x`, it η-expands to `fun (x : A) => s x`
(which it is definitionally equal to by the η rule). -/
def tryEtaExpansionCore (t s : Expr) : RecM Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf (← inferType s) | return false
    isDefEq t (.lam name ty (.app s (.bvar 0)) bi)
  else return false

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : Expr) : RecM Bool :=
  tryEtaExpansionCore t s <||> tryEtaExpansionCore s t

/-- One field comparison in the structure-eta fast path.  Naming the
callback keeps the executable range loop and its verification aligned without
depending on proof terms synthesized by `for` notation. -/
def tryEtaStructFieldStep (t : Expr) (induct : Name) (numParams : Nat)
    (args : Array Expr) (i : Nat) (_ : i ∈ [numParams:args.size])
    (_ : Option Bool × PUnit) :
    RecM (ForInStep (Option Bool × PUnit)) := do
  let b ← isDefEq (.proj induct (i - numParams) t) args[i]
  if b = true then
    pure (.yield ⟨none, PUnit.unit⟩)
  else
    pure (.done ⟨some false, PUnit.unit⟩)

/-- Assuming `t` and `s` in WHNF, checks if they are defeq on account of `s` being defeq to the
struct-η-expansion of `t`.

Assuming that `t` has a non-recursive structure type `S` with constructor `S.mk` and projections
`pᵢ`, it struct-η-expands to `S.mk (p₁ t) ... (pₙ t)` (which it is definitionally equal to by the
struct-η rule). -/
def tryEtaStructCore (t s : Expr) : RecM Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless env.isNonRecStructure fInfo.induct do return false
  unless ← isDefEq (← inferType t) (← inferType s) do return false
  let args := s.getAppArgs
  -- since `t` is in WHNF, and assuming it is not a constructor application, this projection
  -- cannot reduce (so we are directly checking if `s` is defeq to the struct-η-expansion of `t`)
  let r ← forIn' [fInfo.numParams:args.size] ⟨none, PUnit.unit⟩
    (tryEtaStructFieldStep t fInfo.induct fInfo.numParams args)
  match r.1 with
  | none => return true
  | some b => return b

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : Expr) : RecM Bool :=
  -- when `t` and `s` are both constructor applications, `isDefEqApp` has already compared their
  -- arguments and returned false, and the projections in `tryEtaStructCore` reduce back to those
  -- same arguments, so both calls below merely redo that work. The kernel has the same redundancy.
  tryEtaStructCore t s <||> tryEtaStructCore s t

/-- Checks if applications `t` and `s` (should be WHNF) are defeq on account of their function heads
and arguments being defeq. -/
def isDefEqApp (t s : Expr) : RecM Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  if _h : tArgs.size = sArgs.size then
    unless ← isDefEq tf sf do return false
    let rec loop i := do
      if _h : i < tArgs.size then
        unless ← isDefEq tArgs[i] sArgs[i] do return false
        loop (i+1)
      else return true
    loop 0
  else return false

/-- Checks if `t` and `s` are definitionally equivalent according to proof irrelevance (that is,
they are proofs of the same proposition). -/
def isDefEqProofIrrel (t s : Expr) : RecM LBool := do
  let tType ← inferType t
  if !(← isProp tType) then return .undef
  toLBoolM <| isDefEq tType (← inferType s)

def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : Expr) : RecM (Option Expr) := do
  let f := e.getAppFn
  if !f.isProj then return none
  let e' ← whnfCore e
  return if e' != e then e' else none

/-- Performs a single step of δ-reduction on `tn`, `sn`, or both (according to optimizations)
followed by weak-head normalization (without further δ-reduction). Returns `.bool` if the resulting
terms are settled by `quickIsDefEq`, or if they are applications of the same defined constant with
defeq args. Otherwise returns `.continue`, indicating to the calling `lazyDeltaReduction` that
δ-reduction is to be continued.

If neither side has a δ-reducible head, returns `.unknown` with the terms unchanged, leaving further
defeq-checking to `isDefEqCore'`. Note that these are weak-head normal forms with respect to
`cheapProj := true`, so a projection at the head may still be reducible. -/
def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := do whnfCore (← unfoldDefinition e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .bool true
    | .false => .bool false
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    -- `sn` was normalized with `cheapProj := true`, so a projection at its head may not have been
    -- reduced; `tryUnfoldProjApp` retries it with the struct argument fully normalized
    if let some sn' ← tryUnfoldProjApp sn then
      cont tn sn'
    else
      cont (← delta tn) sn
  | none, some _ =>
    if let some tn' ← tryUnfoldProjApp tn then
      cont tn' sn
    else
      cont tn (← delta sn)
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      cont tn (← delta sn)
    else if hs.lt' ht then
      cont (← delta tn) sn
    else
      if tn.isApp && sn.isApp && ptrEqConstantInfo dt ds && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          if ← isDefEqArgs tn sn then
            return .bool true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

/-- Returns `.true` if `t` and `s` are both zero, either as a literal or as `Nat.zero`. If they are
both successors of natural numbers `t'` and `s'`, either as literals or `Nat.succ` applications,
checks that `t'` and `s'` are definitionally equal. Otherwise, defers to the calling function. -/
def isDefEqOffset (t s : Expr) : RecM LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore t' s'
  | _, _ => return .undef

/-- Repeatedly δ-reduces the `cheapProj := true` weak-head normal forms `tn` and `sn` until the
question is settled. Returns `.bool` if:
- they are both zero or both natural number successors (as literals or `Nat.succ` applications)
- one of them can be converted to a natural number/boolean literal
- a `lazyDeltaReductionStep` settles them

Otherwise returns `.unknown` with the reduced terms, deferring to the calling function. Throws
`.deterministicTimeout` after `FuelConfig.lazyDelta` steps. -/
def lazyDeltaReduction (tn sn : Expr) : RecM ReductionStatus := do
  loop tn sn (← readThe Context).fuel.lazyDelta
where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool (r == .true)
    if !tn.hasFVar && !sn.hasFVar || (← readThe Context).eagerReduce then
      if let some tn' ← reduceNat tn then
        return .bool (← isDefEqCore tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool (← isDefEqCore tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      return .bool (← isDefEqCore tn' sn)
    else if let some sn' ← reduceNative env sn then
      return .bool (← isDefEqCore tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

/-- If `t` is a string literal and `s` is a `String.ofList` application, checks that they are defeq
after expanding `t` into a `String.ofList` application of an explicit character list. Otherwise,
defers to the calling function. -/
def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.ofList [] do return .undef
  toLBoolM <| isDefEqCore (.strLitToConstructor st) s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/-- Checks if `t` and `s` are defeq on account of both being of a unit type (a type with one
constructor without any fields or indices). -/
def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf (← inferType t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCore tType (← inferType s)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : Expr) : RecM Bool := do
  let r ← quickIsDefEq t s
  if r != .undef then return r == .true

  if (!t.hasFVar || (← readThe Context).eagerReduce) && s.isConstOf ``true then
    if (← whnf t).isConstOf ``true then return true

  let tn ← whnfCore t (cheapProj := true)
  let sn ← whnfCore s (cheapProj := true)

  if !(ptrEqExpr tn t && ptrEqExpr sn s) then
    let r ← quickIsDefEq tn sn
    if r != .undef then return r == .true

  let r ← isDefEqProofIrrel tn sn
  if r != .undef then return r == .true

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .bool b => return b
  | .unknown tn sn =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj _ ti te, .proj _ si se =>
    -- optimized by the previous reduction functions using `cheapProj := true`
    if ti == si then if ← isDefEq te se then return true
  | _, _ => pure ()

  -- the previous reduction functions used `cheapProj := true`, so we may not have a complete WHNF
  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(ptrEqExpr tnn tn && ptrEqExpr snn sn) then
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    return ← isDefEqCore tnn snn

  -- tn and sn are both in WHNF
  if ← isDefEqApp tn sn then return true
  if ← tryEtaExpansion tn sn then return true
  if ← tryEtaStruct tn sn then return true
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return r == .true
  if ← isDefEqUnitLike tn sn then return true
  return false

end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      whnfCore := fun e p => whnfCore' e p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      inferType := fun e i => inferType' e i (withFuel n) }

/-- Runs `x` with a limit on the recursion depth, taken from `FuelConfig.recDepth`. -/
def RecM.run (x : RecM α) : M α := do x (Methods.withFuel (← readThe Context).fuel.recDepth)

def RecM.runTermElab (x : RecM α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α :=
  x.run.runTermElab safety

instance : MonadLift RecM Elab.Term.TermElabM := ⟨RecM.runTermElab⟩

@[inherit_doc whnf']
def whnf (e : Expr) : M Expr := (Inner.whnf e).run

def whnfCore (e : Expr) : M Expr := (Inner.whnfCore e).run

def unfoldDefinition (e : Expr) : M Expr := return (← (Inner.unfoldDefinition e).run).getD e

/-- Infers the type of expression `e`. Note that this uses the optimization `inferOnly := true`, and
so should only be used for the purpose of type inference on terms that are known to be well-typed.
To typecheck terms for the first time, use `checkType`. -/
def inferType (e : Expr) : M Expr := (Inner.inferType e).run

/-- Infers the type of expression `e` and checks that `e` is well-typed according to Lean's typing
judgment.

Use `inferType` to infer type alone. -/
def checkType (e : Expr) : M Expr := (Inner.inferType e (inferOnly := false)).run

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : M Bool := (Inner.isDefEq t s).run

@[inherit_doc Inner.isProp]
def isProp (t : Expr) : M Bool := (Inner.isProp t).run

@[inherit_doc ensureSortCore]
def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

@[inherit_doc ensureForallCore]
def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

/-- Ensures that `e` is a type/proposition. If it is not, throws an error. -/
def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | it => do
    let itType ← whnf <| ← inferType <| it.instantiateRev fvars
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      withLocalDecl name bi d fun arg => do
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] (← readThe Context).fuel.etaExpand itType
  loop #[] e

-- for testing:

-- example : "hi" = sorry := by
--   run_tac
--     let env ← Lean.getEnv
--     let lctx ← getLCtx
--     let (_, lhs, _) := (← Elab.Tactic.getMainTarget).eq?.get!
--     logInfo lhs
--     let ty ← show M _ from withReader ({· with env := .empty `h}) (inferType lhs)
--     logInfo ty
--     let sort ← inferType ty
--     logInfo sort
