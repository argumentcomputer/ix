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

mutual

partial def infer (e : KExpr m) : RecM m (KExpr m) := do
  let inferOnly := (← get).inferOnly
  let cacheKey ← TcM.inferKey e
  -- Full-mode results are validated; either mode may consume them.
  if let some cached := (← get).env.inferCache[cacheKey]? then
    return cached
  if inferOnly then
    if let some cached := (← get).env.inferOnlyCache[cacheKey]? then
      return cached
  let ty ← match e with
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
      let fTy ← infer f
      let (dom, cod) ← ensureForallDirect fTy
      if !inferOnly then
        let aTy ← infer a
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
        let t ← infer ty
        let _ ← ensureSortDirect t
      -- Open the binder with a fresh fvar (lean4lean inferLambda).
      let saved := (← get).lctx.size
      let fvId ← TcM.freshFVarId (m := m)
      let fv ← TcM.intern (.mkFVar fvId name)
      modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty) }
      let bodyOpen ← TcM.runIntern (instantiateRev body #[fv])
      let bodyTy ← infer bodyOpen
      -- Peephole-reduce App(λ…, …) shapes before wrapping in the Pi.
      let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
      let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fvId])
      modify fun s => { s with lctx := s.lctx.truncate saved }
      -- Anonymous binder metadata (hash-neutral; see module doc).
      TcM.intern (.mkAll anonN anonBi ty abstracted)
    | .all name bi ty body _ => do
      let tyTy ← infer ty
      let u1 ← ensureSortDirect tyTy
      let saved := (← get).lctx.size
      let fvId ← TcM.freshFVarId (m := m)
      let fv ← TcM.intern (.mkFVar fvId name)
      modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty) }
      let bodyOpen ← TcM.runIntern (instantiateRev body #[fv])
      let bodyTy ← infer bodyOpen
      let u2 ← ensureSortDirect bodyTy
      modify fun s => { s with lctx := s.lctx.truncate saved }
      TcM.intern (.mkSort (.mkIMax u1 u2))
    | .letE name ty val body _ _ => do
      if !inferOnly then
        let t ← infer ty
        let _ ← ensureSortDirect t
        let valTy ← infer val
        if !(← isDefEqCall valTy ty) then
          throw .declTypeMismatch
      -- Open with a let-bound fvar (lean4lean inferLet); eagerly substitute
      -- the value into the abstracted body type, then cheap-beta.
      let saved := (← get).lctx.size
      let fvId ← TcM.freshFVarId (m := m)
      let fv ← TcM.intern (.mkFVar fvId name)
      modify fun s => { s with lctx := s.lctx.push fvId (.ldecl name ty val) }
      let bodyOpen ← TcM.runIntern (instantiateRev body #[fv])
      let bodyTy ← infer bodyOpen
      let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fvId])
      let r ← TcM.runIntern (subst abstracted val 0)
      let r ← TcM.runIntern (cheapBetaReduce r)
      modify fun s => { s with lctx := s.lctx.truncate saved }
      pure r
    | .prj structId field val _ => do
      let valTy ← infer val
      inferProj structId field val valTy
    | .nat .. => do TcM.intern (.mkConst (← prims).nat #[])
    | .str .. => do TcM.intern (.mkConst (← prims).string #[])
  if !inferOnly then
    modify fun s => { s with env := { s.env with
      inferCache := s.env.inferCache.insert cacheKey ty } }
  else
    modify fun s => { s with env := { s.env with
      inferOnlyCache := s.env.inferOnlyCache.insert cacheKey ty } }
  return ty

/-- `ensureSort` against the direct whnf (no Methods indirection needed —
    infer imports whnf). -/
partial def ensureSortDirect (e : KExpr m) : RecM m (KUniv m) := do
  if let .sort u _ := e then
    return u
  match (← whnf e) with
  | .sort u _ => return u
  | _ => throw .typeExpected

partial def ensureForallDirect (e : KExpr m) : RecM m (KExpr m × KExpr m) := do
  if let .all _ _ a b _ := e then
    return (a, b)
  let w ← whnf e
  match w with
  | .all _ _ a b _ => return (a, b)
  | _ => throw (.funExpected e w)

/-- The isDefEq back-edge (tied in `Ix.Tc.Knot`). -/
partial def isDefEqCall (a b : KExpr m) : RecM m Bool := do
  (← read).isDefEq a b

partial def inferProj (structId : KId m) (field : UInt64) (val : KExpr m)
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
  let mut r ← TcM.instantiateUnivParams ctorTy iLevels
  for i in [0:numParams] do
    let (_, body) ← peelProjForall r "projection: expected forall in ctor type"
    if h : i < args.size then
      r ← TcM.runIntern (subst body args[i] 0)
    else
      throw (.other "projection: not enough params")
  for i in [0:field.toNat + 1] do
    let (dom, body) ← peelProjForall r "projection: not enough fields"
    if i == field.toNat then
      -- Prop structures may only project Prop fields.
      if isPropStruct then
        let fieldSortTy ← infer dom
        let fieldLevel ← ensureSortDirect fieldSortTy
        if !univEq fieldLevel .mkZero then
          throw (.other "projection: cannot project data field from Prop structure")
      return dom
    if isPropStruct then
      let fieldSortTy ← infer dom
      let fieldLevel ← ensureSortDirect fieldSortTy
      let isData := !univEq fieldLevel .mkZero
      -- body.lbr > 0 ⇒ later fields depend on this one.
      if isData && body.lbr > 0 then
        throw (.other
          "projection: forbidden after dependent data field in Prop structure")
    let proj ← TcM.intern (.mkPrj structId i.toUInt64 val)
    r ← TcM.runIntern (subst body proj 0)
  throw (.other "projection: unreachable")

/-- Peel a leading `Π`: syntactic fast path, whnf fallback. -/
partial def peelProjForall (e : KExpr m) (err : String) :
    RecM m (KExpr m × KExpr m) := do
  if let .all _ _ dom body _ := e then
    return (dom, body)
  match (← whnf e) with
  | .all _ _ dom body _ => return (dom, body)
  | _ => throw (.other err)

partial def inductiveAppIsProp (indId : KId m) (levels : Array (KUniv m))
    (binders : Nat) : RecM m Bool := do
  let indTy ← match (← TcM.tryGetConst indId) with
    | some (.indc (ty := ty) ..) => pure ty
    | _ => throw (.other "projection: not an inductive type")
  let mut r ← TcM.instantiateUnivParams indTy levels
  for _ in [0:binders] do
    let wr ← whnf r
    match wr with
    | .all _ _ _ body _ => r := body
    | _ => throw (.other "projection: expected forall in inductive type")
  let sortTy ← whnf r
  let level ← ensureSortDirect sortTy
  return univEq level .mkZero

end

end RecM

end Ix.Tc

end
end
