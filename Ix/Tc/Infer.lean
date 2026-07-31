module

public import Ix.Tc.Whnf

/-!
Mirror: crates/kernel/src/infer.rs

Type inference. Full mode validates (app argument types, let value types,
binder-domain sorts); infer-only mode (`TcM.withInferOnly`) only synthesizes.

Cache discipline (load-bearing): full-mode results go to `inferCache` and may
be consumed by either mode; infer-only results go to `inferOnlyCache` and are
consulted only while infer-only is active (they skipped validation).

Lambda inference opens the binder with a fresh fvar, infers, cheap-beta
reduces, abstracts, and rewraps with **anonymous** binder metadata (not the
lambda's own name/bi) — recursor coherence relies on this exact shape.
Let inference eagerly substitutes the value into the abstracted body type
(no `letE` wrapper leaks into cached results).
-/

public section
@[expose] section

namespace Ix.Tc

namespace RecM

/-- Store one successful inference result in the cache partition selected by
the validation policy captured at entry.  Keeping this write separate from
the syntax dispatcher gives verification one exact state-update seam without
changing the full/infer-only separation. -/
def cacheInferResult (inferOnly : Bool) (cacheKey : Address × Address)
    (ty : KExpr m) : RecM m Unit := do
  if !inferOnly then
    modify fun s => { s with env := { s.env with
      inferCache := s.env.inferCache.insert cacheKey ty } }
  else
    modify fun s => { s with env := { s.env with
      inferOnlyCache := s.env.inferOnlyCache.insert cacheKey ty } }

mutual

/-- Infer one expression after both policy-appropriate cache partitions have
missed.  Recursive inference and DefEq calls still go through the smaller
method table supplied by the caller. -/
def inferUncached (inferRec : KExpr m → RecM m (KExpr m))
    (inferOnly : Bool) (e : KExpr m) : RecM m (KExpr m) := do
  match e with
    | .var i _ _ =>
      -- Legacy de Bruijn lookup (inductive-validation paths still push via
      -- pushLocal/pushLet).
      TcM.lookupVar (m := m) i
    | .fvar id _ _ =>
      match (← get).lctx.find? id with
      | some decl => pure decl.ty
      | none =>
        throw (.other s!"infer: unknown FVar({id}); not bound in the active local context")
    | .sort u _ =>
      TcM.intern (.mkSort (.mkSucc u))
    | .const id us _ => do
      let c ← TcM.getConst id
      if c.lvls.toNat != us.size then
        throw (.univParamMismatch c.lvls us.size)
      TcM.instantiateUnivParams c.ty us
    | .app f a _ => do
      let fTy ← inferRec f
      let (dom, cod) ← ensureForallDirect fTy
      if !inferOnly then
        let aTy ← inferRec a
        let isEager ← TcM.isEagerReduce a
        if isEager then
          modify fun s => { s with eagerReduce := true }
        -- Error propagation deliberately leaves eagerReduce set (Rust
        -- parity; per-constant reset clears it).
        let eq ← isDefEqCall aTy dom
        if isEager then
          modify fun s => { s with eagerReduce := false }
        if !eq then
          throw (.appTypeMismatch aTy dom (← get).ctx.size)
      TcM.runIntern (subst cod a 0)
    | .lam name bi ty body _ => do
      if !inferOnly then
        let t ← inferRec ty
        let _ ← ensureSortDirect t
      withLctxScope do
        -- Open the binder with a fresh fvar (lean4lean inferLambda).
        let (bodyOpen, fvId) ← TcM.openBinder name bi ty body
        let bodyTy ← inferRec bodyOpen
        -- Peephole-reduce App(λ…, …) shapes before wrapping in the Pi.
        let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fvId])
        -- Anonymous binder metadata (hash-neutral; see module doc).
        TcM.intern (.mkAll anonN anonBi ty abstracted)
    | .all name bi ty body _ => do
      let tyTy ← inferRec ty
      let u1 ← ensureSortDirect tyTy
      withLctxScope do
        let (bodyOpen, _) ← TcM.openBinder name bi ty body
        let bodyTy ← inferRec bodyOpen
        let u2 ← ensureSortDirect bodyTy
        TcM.intern (.mkSort (.mkIMax u1 u2))
    | .letE name ty val body _ _ => do
      if !inferOnly then
        let t ← inferRec ty
        let _ ← ensureSortDirect t
        let valTy ← inferRec val
        if !(← isDefEqCall valTy ty) then
          throw .declTypeMismatch
      -- Open with a let-bound fvar (lean4lean inferLet); eagerly substitute
      -- the value into the abstracted body type, then cheap-beta.
      withLctxScope do
        let (bodyOpen, fvId) ← TcM.openLet name ty val body
        let bodyTy ← inferRec bodyOpen
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fvId])
        let r ← TcM.runIntern (subst abstracted val 0)
        TcM.runIntern (cheapBetaReduce r)
    | .prj structId field val _ => do
      let valTy ← inferRec val
      inferProj structId field val valTy
    | .nat .. => do TcM.intern (.mkConst (← prims).nat #[])
    | .str .. => do TcM.intern (.mkConst (← prims).string #[])

def inferWith (inferRec : KExpr m → RecM m (KExpr m))
    (e : KExpr m) : RecM m (KExpr m) := do
  let inferOnly := (← get).inferOnly
  let cacheKey ← TcM.inferKey e
  -- Full-mode results are validated; either mode may consume them.
  if let some cached := (← get).env.inferCache[cacheKey]? then
    return cached
  if inferOnly then
    if let some cached := (← get).env.inferOnlyCache[cacheKey]? then
      return cached
  let ty ← inferUncached inferRec inferOnly e
  cacheInferResult inferOnly cacheKey ty
  return ty

/-- One recursive Infer edge through the indexed method table. -/
@[inline] def inferCall (e : KExpr m) : RecM m (KExpr m) := do
  (← read).infer e

/-- One recursive Infer edge with Infer-only validation policy scoped around
    the underlying `TcM` action. -/
@[inline] def inferOnlyCall (e : KExpr m) : RecM m (KExpr m) := do
  let methods ← read
  TcM.withInferOnly (methods.infer e)

/-- Tie Infer's structural recursive calls through the indexed method table.
    `inferWith` is the transparent one-layer body consumed by K0/K1 proofs. -/
def infer (e : KExpr m) : RecM m (KExpr m) :=
  inferWith inferCall e

/-- WHNF fallback for sort exposure.  Naming the fallback separately keeps
the syntactic fast path in `ensureSortDirect` while giving verification an
exact target for the reduction-dependent branch. -/
def ensureSortWhnf (e : KExpr m) : RecM m (KUniv m) := do
  match (← whnf e) with
  | .sort u _ => return u
  | _ => throw .typeExpected

/-- `ensureSort` against the direct whnf (no Methods indirection needed —
    infer imports whnf). -/
def ensureSortDirect (e : KExpr m) : RecM m (KUniv m) := do
  if let .sort u _ := e then
    return u
  ensureSortWhnf e

def ensureForallWhnf (e : KExpr m) : RecM m (KExpr m × KExpr m) := do
  let w ← whnf e
  match w with
  | .all _ _ a b _ => return (a, b)
  | _ => throw (.funExpected e w)

/-- Syntactic Pi fast path with a separately named WHNF fallback.  The seam
is operationally neutral and gives verification an exact target for the
non-syntactic branch. -/
def ensureForallDirect (e : KExpr m) : RecM m (KExpr m × KExpr m) := do
  if let .all _ _ a b _ := e then
    return (a, b)
  ensureForallWhnf e

/-- The isDefEq back-edge (tied in `Ix.Tc.Knot`). -/
def isDefEqCall (a b : KExpr m) : RecM m Bool := do
  (← read).isDefEq a b

/-- One constructor-parameter iteration.  The explicit `ForInStep` result
makes the state threaded by the production range loop visible to proofs. -/
def instantiateProjParamStep (args : Array (KExpr m)) (i : Nat)
    (ctorTy : KExpr m) : RecM m (ForInStep (KExpr m)) := do
  let (_, body) ← peelProjForall ctorTy
    "projection: expected forall in ctor type"
  if h : i < args.size then
    let result ← TcM.runIntern (subst body args[i] 0)
    return .yield result
  else
    throw (.other "projection: not enough params")

/-- Instantiate the constructor telescope's inductive parameters with the
arguments recovered from the projected value's inferred type.  Naming this
loop separately exposes its exact partial-error boundary to verification. -/
def instantiateProjParams (args : Array (KExpr m)) (numParams : Nat)
    (ctorTy : KExpr m) : RecM m (KExpr m) :=
  forIn [0:numParams] ctorTy (instantiateProjParamStep args)

/-- One constructor-field iteration.  A selected field stops the surrounding
range loop; an earlier field yields the telescope obtained by substituting
the concrete projection node. -/
def inferProjFieldStep (structId : KId m) (field : UInt64) (val : KExpr m)
    (isPropStruct : Bool) (i : Nat) (current : KExpr m) :
    RecM m (ForInStep (KExpr m)) := do
  let (dom, body) ←
    peelProjForall current "projection: not enough fields"
  if i == field.toNat then
    -- Prop structures may only project Prop fields.
    if isPropStruct then
      let fieldSortTy ← inferCall dom
      let fieldLevel ← ensureSortDirect fieldSortTy
      if !univEq fieldLevel .mkZero then
        throw (.other
          "projection: cannot project data field from Prop structure")
    return .done dom
  if isPropStruct then
    let fieldSortTy ← inferCall dom
    let fieldLevel ← ensureSortDirect fieldSortTy
    let isData := !univEq fieldLevel .mkZero
    -- body.lbr > 0 ⇒ later fields depend on this one.
    if isData && body.lbr > 0 then
      throw (.other
        "projection: forbidden after dependent data field in Prop structure")
  let proj ← TcM.intern (.mkPrj structId i.toUInt64 val)
  let result ← TcM.runIntern (subst body proj 0)
  return .yield result

/-- Lift a field step into the accumulator used by the projection range
loop.  A selected field stores its result and stops; an earlier field stores
the substituted telescope and continues. -/
def inferProjFieldsLoopStep (structId : KId m) (field : UInt64)
    (val : KExpr m) (isPropStruct : Bool) (i : Nat)
    (state : Option (KExpr m) × KExpr m) :
    RecM m (ForInStep (Option (KExpr m) × KExpr m)) := do
  match ← inferProjFieldStep structId field val isPropStruct i state.2 with
  | .done result =>
      pure (.done (some result, state.2))
  | .yield next =>
      pure (.yield (none, next))

/-- Walk the instantiated constructor fields up to the requested projection.
Earlier dependent fields are substituted by concrete projection nodes; Prop
elimination checks are performed at the same points as the original inline
loop. -/
def inferProjFields (structId : KId m) (field : UInt64) (val : KExpr m)
    (isPropStruct : Bool) (ctorTy : KExpr m) : RecM m (KExpr m) := do
  let state ← forIn [0:field.toNat + 1]
    ((none : Option (KExpr m)), ctorTy)
    (inferProjFieldsLoopStep structId field val isPropStruct)
  match state.1 with
  | none => throw (.other "projection: unreachable")
  | some result => pure result

def inferProj (structId : KId m) (field : UInt64) (val : KExpr m)
    (valTy : KExpr m) : RecM m (KExpr m) := do
  let wty ← whnf valTy
  let (head, args) := wty.collectSpine
  let .const headId iLevels _ := head
    | throw (.other "projection: struct type is not a constant")
  if headId.addr != structId.addr then
    throw (.other "projection: type mismatch with declared struct")
  let (numParams, numIndices, ctors) ← match (← TcM.tryGetConst headId) with
    | some (.indc (params := params) (indices := indices) (ctors := ctors) ..) =>
      pure (params.toNat, indices.toNat, ctors)
    | _ => throw (.other "projection: not an inductive type")
  if ctors.size != 1 then
    throw (.other "projection: inductive must have exactly one constructor")
  -- Prop check from the declaration's result sort (not the applied value).
  let isPropStruct ← inductiveAppIsProp headId iLevels (numParams + numIndices)
  let ctorTy ← match (← TcM.tryGetConst ctors[0]!) with
    | some c => pure c.ty
    | none => throw (.other "projection: constructor not found")
  let instantiatedCtorTy ← TcM.instantiateUnivParams ctorTy iLevels
  let parameterizedCtorTy ←
    instantiateProjParams args numParams instantiatedCtorTy
  inferProjFields structId field val isPropStruct parameterizedCtorTy

/-- Peel a leading `Π`: syntactic fast path, whnf fallback. -/
def peelProjForall (e : KExpr m) (err : String) :
    RecM m (KExpr m × KExpr m) := do
  if let .all _ _ dom body _ := e then
    return (dom, body)
  match (← whnf e) with
  | .all _ _ dom body _ => return (dom, body)
  | _ => throw (.other err)

/-- One declaration-binder scan used while classifying an inductive result
sort.  The body is intentionally not instantiated: production only needs the
eventual sort and therefore carries the raw declaration telescope. -/
def inductiveAppBinderStep (current : KExpr m) :
    RecM m (ForInStep (KExpr m)) := do
  let reduced ← whnf current
  match reduced with
  | .all _ _ _ body _ => pure (.yield body)
  | _ => throw (.other "projection: expected forall in inductive type")

/-- Strip the declared parameter and index prefix before inspecting an
inductive family's result sort. -/
def inductiveAppBinders (binders : Nat) (indTy : KExpr m) :
    RecM m (KExpr m) :=
  forIn [0:binders] indTy (fun _ current =>
    inductiveAppBinderStep current)

/-- Classify the result remaining after the declaration telescope has been
stripped. -/
def inductiveAppResultIsProp (resultTy : KExpr m) : RecM m Bool := do
  let sortTy ← whnf resultTy
  let level ← ensureSortDirect sortTy
  return univEq level .mkZero

def inductiveAppIsProp (indId : KId m) (levels : Array (KUniv m))
    (binders : Nat) : RecM m Bool := do
  let indTy ← match (← TcM.tryGetConst indId) with
    | some (.indc (ty := ty) ..) => pure ty
    | _ => throw (.other "projection: not an inductive type")
  let instantiated ← TcM.instantiateUnivParams indTy levels
  let resultTy ← inductiveAppBinders binders instantiated
  inductiveAppResultIsProp resultTy

end

end RecM

end Ix.Tc

end
end
