module

public import Ix.Tc.Infer

/-!
Mirror: crates/kernel/src/def_eq.rs

Multi-tier definitional equality (lean4lean shape):
1. quick structural (hash / binder common-fvar opening)
1b. eager Bool.true reduction; 1c. string-literal expansion **before any
    whnf**; 1d. cheap whnf-core then cheap whnf-no-delta passes
3. proof irrelevance (before delta), with the `isPropCache`
4. iterative lazy delta with ReducibilityHints ranking, tryUnfoldProjApp,
   and the same-head-spine attempt whose failures populate the
   `defEqFailure` negative cache — ONLY there (generalizing it is a
   completeness bug)
4b. post-delta structural congruence (Const/Var/Prj with proj-delta loop)
4c. second structural pass via `whnfCore` — deliberately NOT full whnf
4d. app-spine comparison
5. full structural + nat-literal bridging + eta + string expansion +
   struct-eta + unit-like + proof irrelevance

Cache discipline at the entry point: cheap-mode `false` goes only to the
cheap cache; cheap `true` promotes to the full cache and the EquivManager
(monotone-sound). Fuel is charged only after the O(1) exits.
-/

public section
@[expose] section

namespace Ix.Tc

/-- Lazy-delta single-step outcome. -/
inductive LazyDeltaStep where
  | equal
  | continue'
  | unknown
  deriving BEq, Repr, Inhabited

/-- Canonically ordered address pair (byte-lexicographic). -/
def canonicalPair (a b : Address) : Address × Address :=
  if a.cmpBytes b != .gt then (a, b) else (b, a)

/-- Head constant of an expression or app spine. -/
def headConstId (e : KExpr m) : Option (KId m) :=
  match e with
  | .const id _ _ => some id
  | .app .. =>
    match e.collectSpine with
    | (.const id _ _, _) => some id
    | _ => none
  | _ => none

namespace RecM

mutual

/-- Definitional equality entry point: fast paths, equiv-manager, caches
    (with cheap-mode routing), fuel/depth accounting, then the tiers. -/
partial def isDefEq (a b : KExpr m) : RecM m Bool := do
  if a.addr == b.addr then
    -- Hashes are alpha-invariant in both modes; this is the only
    -- structural alpha-equivalence fast path needed.
    return true
  let eqCtx ← TcM.defEqCtxKey a b
  let aKey : EqKey := (a.addr, eqCtx)
  let bKey : EqKey := (b.addr, eqCtx)
  let (isEq, em) := (← get).equivManager.isEquiv aKey bKey
  modify fun s => { s with equivManager := em }
  if isEq then
    return true
  let (lo, hi) := canonicalPair a.addr b.addr
  let cacheKey := (lo, hi, eqCtx)
  let cheapMode := (← get).cheapRecursionDepth > 0
  if let some cached := (← get).env.defEqCache[cacheKey]? then
    if cheapMode then
      modify fun s => { s with env := { s.env with
        defEqCheapCache := s.env.defEqCheapCache.insert cacheKey cached } }
    if cached then
      modify fun s => { s with
        equivManager := s.equivManager.addEquiv aKey bKey }
    return cached
  if cheapMode then
    if let some cached := (← get).env.defEqCheapCache[cacheKey]? then
      if cached then
        modify fun s => { s with
          env := { s.env with
            defEqCache := s.env.defEqCache.insert cacheKey true }
          equivManager := s.equivManager.addEquiv aKey bKey }
      return cached
  -- Equiv-root second chance: probe (root a, root b).
  let (aRoot?, em) := (← get).equivManager.findRootKey aKey
  let (bRoot?, em) := em.findRootKey bKey
  modify fun s => { s with equivManager := em }
  if let (some aRoot, some bRoot) := (aRoot?, bRoot?) then
    if aRoot != aKey || bRoot != bKey then
      -- EqKey is (exprAddr, ctxAddr); canonicalize the expr components.
      let (rlo, rhi) := canonicalPair aRoot.fst bRoot.fst
      let rootCacheKey := (rlo, rhi, eqCtx)
      let cached? : Option (Bool × Bool) ←
        match (← get).env.defEqCache[rootCacheKey]? with
        | some v => pure (some (v, false))
        | none =>
          if cheapMode then
            match (← get).env.defEqCheapCache[rootCacheKey]? with
            | some v => pure (some (v, true))
            | none => pure none
          else
            pure none
      if let some (cached, fromCheap) := cached? then
        if fromCheap then
          modify fun s => { s with env := { s.env with
            defEqCheapCache := s.env.defEqCheapCache.insert cacheKey cached
            defEqCache := if cached then
                s.env.defEqCache.insert cacheKey true
              else s.env.defEqCache } }
        else
          modify fun s => { s with env := { s.env with
            defEqCache := s.env.defEqCache.insert cacheKey cached
            defEqCheapCache := if cheapMode then
                s.env.defEqCheapCache.insert cacheKey cached
              else s.env.defEqCheapCache } }
        if cached then
          modify fun s => { s with
            equivManager := s.equivManager.addEquiv aKey bKey }
        return cached
  -- Charge fuel only after the O(1) exits.
  TcM.tick (m := m)
  modify fun s => { s with
    defEqDepth := s.defEqDepth + 1
    defEqPeak := max s.defEqPeak (s.defEqDepth + 1) }
  if (← get).defEqDepth > maxDefEqDepth then
    modify fun s => { s with defEqDepth := s.defEqDepth - 1 }
    throw .maxRecDepth
  let result ←
    try
      let r ← isDefEqInner a b
      pure (Except.ok r)
    catch e =>
      pure (Except.error e)
  modify fun s => { s with defEqDepth := s.defEqDepth - 1 }
  let ok ← match result with
    | .ok r => pure r
    | .error e => throw e
  if ok then
    -- Cheap-mode `true` is monotone (cheap-equal ⇒ FULL-equal).
    modify fun s => { s with
      equivManager := s.equivManager.addEquiv aKey bKey }
  if cheapMode then
    modify fun s => { s with env := { s.env with
      defEqCheapCache := s.env.defEqCheapCache.insert cacheKey ok
      defEqCache := if ok then s.env.defEqCache.insert cacheKey true
        else s.env.defEqCache } }
  else
    modify fun s => { s with env := { s.env with
      defEqCache := s.env.defEqCache.insert cacheKey ok } }
  return ok

partial def isDefEqInner (a b : KExpr m) : RecM m Bool := do
  -- Tier 1: quick structural.
  if (← quickDefEq a b) then
    return true
  -- Tier 1b: eager Bool.true reduction.
  if (← isBoolTrue b) && (!a.hasFVars || (← get).eagerReduce) then
    if (← isBoolTrue (← whnf a)) then
      return true
  else if (← isBoolTrue a) && (!b.hasFVars || (← get).eagerReduce) then
    if (← isBoolTrue (← whnf b)) then
      return true
  -- Tier 1c: string-literal expansion BEFORE any whnf.
  let aIsStr := match a with | .str .. => true | _ => false
  let bIsStr := match b with | .str .. => true | _ => false
  if aIsStr || bIsStr then
    if (← tryStringLitExpansion a b) then
      return true
    if (← tryStringLitExpansion b a) then
      return true
  -- Tier 1d: cheap structural passes.
  let ca ← whnfCoreForDefEq a
  let cb ← whnfCoreForDefEq b
  if ca.addr == cb.addr then
    return true
  if (← quickDefEq ca cb) then
    return true
  let mut wa ← whnfNoDeltaForDefEq a
  let mut wb ← whnfNoDeltaForDefEq b
  if wa.addr == wb.addr then
    return true
  if (← quickDefEq wa wb) then
    return true
  -- Tier 3: proof irrelevance (before delta).
  if (← tryProofIrrel wa wb) then
    return true
  -- Tier 4: iterative lazy delta.
  let mut fuel := maxWhnfFuel
  let mut broke := false
  repeat
    if fuel == 0 then
      throw .maxRecDepth
    fuel := fuel - 1
    -- Nat offset comparison at the top of the loop.
    if let some result ← tryDefEqOffset wa wb then
      return result
    -- Nat primitives gated on closed terms (or eagerReduce).
    let natOk := (!wa.hasFVars && !wb.hasFVars) || (← get).eagerReduce
    if natOk then
      if let some wa2 ← tryReduceNat wa then
        return (← isDefEq wa2 wb)
      if let some wb2 ← tryReduceNat wb then
        return (← isDefEq wa wb2)
    if let some wa2 ← tryReduceNative wa then
      return (← isDefEq wa2 wb)
    if let some wb2 ← tryReduceNative wb then
      return (← isDefEq wa wb2)
    if let some wa2 ← tryReduceDecidable wa then
      return (← isDefEq wa2 wb)
    if let some wb2 ← tryReduceDecidable wb then
      return (← isDefEq wa wb2)
    let aHead := headConstId wa
    let bHead := headConstId wb
    let aDelta ← match aHead with
      | some h => isDelta h
      | none => pure false
    let bDelta ← match bHead with
      | some h => isDelta h
      | none => pure false
    if !aDelta && !bDelta then
      broke := true
      break
    -- Before unfolding, try reducing projection apps on the other side.
    if aDelta && !bDelta then
      if let some wb2 ← tryUnfoldProjApp wb then
        wb := wb2
        continue
    else if bDelta && !aDelta then
      if let some wa2 ← tryUnfoldProjApp wa then
        wa := wa2
        continue
    if aDelta && bDelta then
      let waW ← match aHead with
        | some h => defRankId h
        | none => pure (255, 4294967295)
      let wbW ← match bHead with
        | some h => defRankId h
        | none => pure (255, 4294967295)
      if waW == wbW then
        -- Same-head-spine attempt, guarded by the narrow negative cache.
        if let (some ah, some bh) := (aHead, bHead) then
          if ah.addr == bh.addr && (← isRegular ah) then
            let (flo, fhi) := canonicalPair wa.addr wb.addr
            let failureKey := (flo, fhi, ← TcM.defEqCtxKey wa wb)
            if !(← get).env.defEqFailure.contains failureKey then
              if let some result ← trySameHeadSpine wa wb then
                return result
              -- Attempted and failed — record.
              modify fun s => { s with env := { s.env with
                defEqFailure := s.env.defEqFailure.insert failureKey } }
        -- Equal rank: unfold BOTH sides.
        let ua ← deltaUnfoldOne wa
        let ub ← deltaUnfoldOne wb
        match ua, ub with
        | some ua, some ub =>
          wa ← whnfNoDeltaForDefEq ua
          wb ← whnfNoDeltaForDefEq ub
        | some ua, none =>
          wa ← whnfNoDeltaForDefEq ua
        | none, some ub =>
          wb ← whnfNoDeltaForDefEq ub
        | none, none =>
          broke := true
          break
      else if compareRank waW wbW == .gt then
        match (← deltaUnfoldOne wa) with
        | some ua => wa ← whnfNoDeltaForDefEq ua
        | none =>
          broke := true
          break
      else
        match (← deltaUnfoldOne wb) with
        | some ub => wb ← whnfNoDeltaForDefEq ub
        | none =>
          broke := true
          break
    else if aDelta then
      match (← deltaUnfoldOne wa) with
      | some ua => wa ← whnfNoDeltaForDefEq ua
      | none =>
        broke := true
        break
    else
      match (← deltaUnfoldOne wb) with
      | some ub => wb ← whnfNoDeltaForDefEq ub
      | none =>
        broke := true
        break
    if wa.addr == wb.addr then
      return true
    if (← quickDefEq wa wb) then
      return true
  let _ := broke
  -- Tier 4b: post-delta structural congruence.
  if (← tryStructuralCongruence wa wb) then
    return true
  -- Tier 4c: second structural pass — whnfCore, NOT full whnf.
  let waCore ← whnfCore wa
  let wbCore ← whnfCore wb
  let waChanged := waCore.addr != wa.addr
  let wbChanged := wbCore.addr != wb.addr
  if waChanged || wbChanged then
    return (← isDefEq waCore wbCore)
  if waCore.addr == wbCore.addr then
    return true
  if (← quickDefEq waCore wbCore) then
    return true
  -- Tier 4d: app-spine comparison.
  if (← tryDefEqApp waCore wbCore) then
    return true
  isDefEqWhnf waCore wbCore

/-- Lexicographic rank comparison ((class, height) tuples). -/
partial def compareRank (a b : Nat × Nat) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

/-- Tier-1 quick structural: same ctor, same children (binders open both
    bodies with the SAME fresh fvar — the common-fvar trick). -/
partial def quickDefEq (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .sort u1 _, .sort u2 _ => return univEq u1 u2
  | .lam name bi ty1 body1 _, .lam _ _ ty2 body2 _ =>
    quickBinder name bi ty1 body1 ty2 body2
  | .all name bi ty1 body1 _, .all _ _ ty2 body2 _ =>
    quickBinder name bi ty1 body1 ty2 body2
  | _, _ => return false

partial def quickBinder (name : m.F Name) (bi : m.F Lean.BinderInfo)
    (ty1 body1 ty2 body2 : KExpr m) : RecM m Bool := do
  if !(← isDefEq ty1 ty2) then
    return false
  let saved := (← get).lctx.size
  let fvId ← TcM.freshFVarId (m := m)
  let fv ← TcM.intern (.mkFVar fvId name)
  modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi ty1) }
  let b1Open ← TcM.runIntern (instantiateRev body1 #[fv])
  let b2Open ← TcM.runIntern (instantiateRev body2 #[fv])
  let r ←
    try
      let r ← isDefEq b1Open b2Open
      pure (Except.ok r)
    catch e =>
      pure (Except.error e)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  match r with
  | .ok v => return v
  | .error e => throw e

/-- Both are `C us args` with the same head: compare spines without
    unfolding. `none` means "not applicable / spine differs". -/
partial def trySameHeadSpine (a b : KExpr m) : RecM m (Option Bool) := do
  let (aHead, aArgs) := a.collectSpine
  let (bHead, bArgs) := b.collectSpine
  let .const aId aUs _ := aHead | return none
  let .const bId bUs _ := bHead | return none
  if aId.addr != bId.addr || aArgs.size != bArgs.size then
    return none
  if aUs.size != bUs.size then
    return none
  for (u, v) in aUs.zip bUs do
    if !univEq u v then
      return none
  for (ai, bi) in aArgs.zip bArgs do
    if !(← isDefEq ai bi) then
      return none
  return some true

/-- Tier 5: full structural + eta / struct-eta / unit / proof irrelevance. -/
partial def isDefEqWhnf (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .sort u1 _, .sort u2 _ => return univEq u1 u2
  | .var i _ _, .var j _ _ =>
    if i == j then
      return true
  | .const id1 us1 _, .const id2 us2 _ =>
    if id1.addr == id2.addr && us1.size == us2.size
        && (us1.zip us2).all (fun (u, v) => univEq u v) then
      return true
  | .app f1 a1 _, .app f2 a2 _ =>
    if (← isDefEq f1 f2) && (← isDefEq a1 a2) then
      return true
  | .lam name bi ty1 body1 _, .lam _ _ ty2 body2 _ =>
    if (← quickBinder name bi ty1 body1 ty2 body2) then
      return true
  | .all name bi ty1 body1 _, .all _ _ ty2 body2 _ =>
    if (← quickBinder name bi ty1 body1 ty2 body2) then
      return true
  | .letE name ty1 v1 body1 _ _, .letE _ ty2 v2 body2 _ _ =>
    -- Normally zeta-reduced before reaching here; push LDecl in case.
    if (← isDefEq ty1 ty2) && (← isDefEq v1 v2) then
      let saved := (← get).lctx.size
      let fvId ← TcM.freshFVarId (m := m)
      let fv ← TcM.intern (.mkFVar fvId name)
      modify fun s => { s with lctx := s.lctx.push fvId (.ldecl name ty1 v1) }
      let b1Open ← TcM.runIntern (instantiateRev body1 #[fv])
      let b2Open ← TcM.runIntern (instantiateRev body2 #[fv])
      let r ← isDefEq b1Open b2Open
      modify fun s => { s with lctx := s.lctx.truncate saved }
      if r then
        return true
  | .nat v1 _ _, .nat v2 _ _ => return v1 == v2
  | .str v1 _ _, .str v2 _ _ => return v1 == v2
  | _, _ => pure ()
  -- Nat literal ↔ constructor bridging.
  if (← isNatLike a) && (← isNatLike b) then
    return (← isDefEqNat a b)
  -- Eta expansion, both directions.
  let aIsLam := match a with | .lam .. => true | _ => false
  let bIsLam := match b with | .lam .. => true | _ => false
  if aIsLam || bIsLam then
    if (← tryEtaExpansion a b) then
      return true
    if (← tryEtaExpansion b a) then
      return true
  -- String literal expansion.
  let aIsStr := match a with | .str .. => true | _ => false
  let bIsStr := match b with | .str .. => true | _ => false
  if aIsStr || bIsStr then
    if (← tryStringLitExpansion a b) then
      return true
    if (← tryStringLitExpansion b a) then
      return true
  -- Struct eta + unit-like + proof irrelevance.
  if (← tryEtaStruct a b) then
    return true
  if (← tryEtaStruct b a) then
    return true
  if (← tryDefEqUnit a b) then
    return true
  tryProofIrrel a b

/-- Proof irrelevance: both proofs of the same Prop. -/
partial def tryProofIrrel (a b : KExpr m) : RecM m Bool := do
  let some aTy ← try? (TcM.withInferOnly ((← read).infer a)) | return false
  if !(← isPropType aTy) then
    return false
  let some bTy ← try? (TcM.withInferOnly ((← read).infer b)) | return false
  isDefEq aTy bTy

/-- Is `ty : Sort 0`? Memoized on `(tyAddr, ctxAddr)`; inner-chain errors
    treated as non-prop. -/
partial def isPropType (ty : KExpr m) : RecM m Bool := do
  let cacheKey := (ty.addr, ← TcM.ctxAddrForLbr (m := m) ty.lbr)
  if let some cached := (← get).env.isPropCache[cacheKey]? then
    return cached
  let result ← (do
    match (← try? (TcM.withInferOnly ((← read).infer ty))) with
    | none => pure false
    | some sort =>
      match (← try? (whnf sort)) with
      | some (.sort u _) => pure u.isZero
      | _ => pure false)
  modify fun s => { s with env := { s.env with
    isPropCache := s.env.isPropCache.insert cacheKey result } }
  return result

/-- Unit-like (non-recursive, 0 indices, 1 nullary ctor): any two
    inhabitants of the same unit-like type are def-eq. -/
partial def tryDefEqUnit (a b : KExpr m) : RecM m Bool := do
  let some aTy ← try? (TcM.withInferOnly ((← read).infer a)) | return false
  let some aTyW ← try? (whnf aTy) | return false
  let (aHead, _) := aTyW.collectSpine
  let .const aInd _ _ := aHead | return false
  let isUnit ← match (← TcM.tryGetConst aInd) with
    | some (.indc (indices := indices) (ctors := ctors) ..) =>
      if indices != 0 || ctors.size != 1 then
        pure false
      else
        match (← TcM.tryGetConst ctors[0]!) with
        | some (.ctor (fields := fields) ..) => pure (fields == 0)
        | _ => pure false
    | _ => return false
  if !isUnit then
    return false
  let some bTy ← try? (TcM.withInferOnly ((← read).infer b)) | return false
  isDefEq aTyW bTy

partial def isNatLike (e : KExpr m) : RecM m Bool := do
  let p ← prims
  match e with
  | .nat .. => return true
  | .const id _ _ => return id.addr == p.natZero.addr
  | .app f _ _ =>
    match f with
    | .const id _ _ => return id.addr == p.natSucc.addr
    | _ => return false
  | _ => return false

partial def isNatZero (e : KExpr m) : RecM m Bool := do
  let p ← prims
  match e with
  | .nat v _ _ => return v == 0
  | .const id _ _ => return id.addr == p.natZero.addr
  | _ => return false

partial def natSuccOf (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let p ← prims
  match e with
  | .nat v _ _ =>
    if v == 0 then
      return none
    return some (← TcM.intern (natExprFromValue (v - 1) : KExpr m))
  | .app f arg _ =>
    match f with
    | .const id _ _ =>
      if id.addr == p.natSucc.addr then
        return some arg
      return none
    | _ => return none
  | _ => return none

/-- Nat-like comparison: literal fast path, zero/succ peeling. -/
partial def isDefEqNat (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .nat va _ _, .nat vb _ _ => return va == vb
  | _, _ => pure ()
  if (← isNatZero a) && (← isNatZero b) then
    return true
  match (← natSuccOf a), (← natSuccOf b) with
  | some aPred, some bPred => isDefEq aPred bPred
  | _, _ => return false

/-- Nat offset comparison in the lazy delta loop (`isDefEqOffset`). -/
partial def tryDefEqOffset (a b : KExpr m) : RecM m (Option Bool) := do
  match a, b with
  | .nat va _ _, .nat vb _ _ => return some (va == vb)
  | _, _ => pure ()
  if (← isNatZero a) && (← isNatZero b) then
    return some true
  match (← natSuccOf a), (← natSuccOf b) with
  | some aPred, some bPred => return some (← isDefEq aPred bPred)
  | _, _ => return none

/-- Expand a string literal to ctor form and compare. -/
partial def tryStringLitExpansion (t s : KExpr m) : RecM m Bool := do
  let .str strVal _ _ := t | return false
  let expanded ← strLitToConstructor strVal
  isDefEq expanded s

/-- Lambda eta: `t` a lambda, `s` not — wrap `s` as `λ(ty). s #0`. -/
partial def tryEtaExpansion (t s : KExpr m) : RecM m Bool := do
  let tIsLam := match t with | .lam .. => true | _ => false
  let sIsLam := match s with | .lam .. => true | _ => false
  if !tIsLam || sIsLam then
    return false
  let some sTy ← try? (TcM.withInferOnly ((← read).infer s)) | return false
  let some sTyWhnf ← try? (whnf sTy) | return false
  let .all name bi ty _ _ := sTyWhnf | return false
  let sLifted ← TcM.runIntern (lift s 1 0)
  let v0 ← TcM.intern (.mkVar 0 anonN : KExpr m)
  let body ← TcM.intern (KExpr.mkApp sLifted v0)
  let sLam ← TcM.intern (.mkLam name bi ty body)
  isDefEq t sLam

/-- Struct eta: `s` a fully-applied ctor of a struct-like type; compare
    `prj i t ≡ s.args[params+i]` per field (types def-eq first; no Prop
    guard here — equality checking, not term construction). -/
partial def tryEtaStruct (t s : KExpr m) : RecM m Bool := do
  let tNorm ← (do
    match (← try? (whnfNoDelta t)) with
    | some w => pure w
    | none => pure t)
  let (sHead, sArgs) := s.collectSpine
  let .const ctorId _ _ := sHead | return false
  let (inductId, numParams, numFields) ← match (← TcM.tryGetConst ctorId) with
    | some (.ctor (induct := induct) (params := params) (fields := fields) ..) =>
      pure (induct, params.toNat, fields.toNat)
    | _ => return false
  if sArgs.size != numParams + numFields then
    return false
  if !(← isStructLike inductId) then
    return false
  let some sTy ← try? (TcM.withInferOnly ((← read).infer s)) | return false
  let some tTy ← try? (TcM.withInferOnly ((← read).infer tNorm)) | return false
  if !(← isDefEq tTy sTy) then
    return false
  if let some base ← etaExpansionBase inductId numParams numFields sArgs then
    if (← isDefEq tNorm base) then
      return true
  for i in [0:numFields] do
    let proj ← TcM.intern (.mkPrj inductId i.toUInt64 tNorm)
    if !(← isDefEq proj sArgs[numParams + i]!) then
      return false
  return true

/-- If every ctor field is `prj i base` of one common base, return it. -/
partial def etaExpansionBase (inductId : KId m) (numParams numFields : Nat)
    (args : Array (KExpr m)) : RecM m (Option (KExpr m)) := do
  let mut base : Option (KExpr m) := none
  for i in [0:numFields] do
    let field := args[numParams + i]!
    let field ← whnfNoDelta field
    let .prj id idx val _ := field | return none
    if id.addr != inductId.addr || idx.toNat != i then
      return none
    let val ← (do
      match (← try? (whnfNoDelta val)) with
      | some w => pure w
      | none => pure val)
    match base with
    | some b =>
      if b.addr != val.addr then
        return none
    | none => base := some val
  return base

/-- App-spine comparison (isDefEqApp). -/
partial def tryDefEqApp (a b : KExpr m) : RecM m Bool := do
  let aIsApp := match a with | .app .. => true | _ => false
  let bIsApp := match b with | .app .. => true | _ => false
  if !aIsApp || !bIsApp then
    return false
  let (aHead, aArgs) := a.collectSpine
  let (bHead, bArgs) := b.collectSpine
  if aArgs.size != bArgs.size then
    return false
  if !(← isDefEq aHead bHead) then
    return false
  for (ai, bi) in aArgs.zip bArgs do
    if !(← isDefEq ai bi) then
      return false
  return true

partial def isBoolTrue (e : KExpr m) : RecM m Bool := do
  match e with
  | .const id us _ =>
    return us.isEmpty && id.addr == (← prims).boolTrue.addr
  | _ => return false

/-- Is the constant delta-reducible (Definition/Theorem)? -/
partial def isDelta (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.defn (kind := kind) ..) =>
    match kind with
    | .defn | .thm => return true
    | .opaq => return false
  | _ => return false

/-- Regular reducibility hints (guards the same-head-spine attempt). -/
partial def isRegular (id : KId m) : RecM m Bool := do
  match (← TcM.tryGetConst id) with
  | some (.defn (hints := .regular _) ..) => return true
  | _ => return false

/-- Reducibility rank `(class, height)`, lexicographic; higher unfolds
    first. Opaque/Theorem/unknown `(0,0)`; `Regular h` `(1,h)`;
    `Abbrev` `(2,0)`. -/
partial def defRankId (id : KId m) : RecM m (Nat × Nat) := do
  match (← TcM.tryGetConst id) with
  | some (.defn (kind := kind) (hints := hints) ..) =>
    match kind with
    | .opaq | .thm => return (0, 0)
    | .defn =>
      match hints with
      | .opaque => return (0, 0)
      | .regular h => return (1, h.toNat)
      | .abbrev => return (2, 0)
  | _ => return (0, 0)

/-- Post-delta structural congruence (Const/Var/Prj). -/
partial def tryStructuralCongruence (a b : KExpr m) : RecM m Bool := do
  match a, b with
  | .const id1 us1 _, .const id2 us2 _ =>
    return id1.addr == id2.addr && us1.size == us2.size
      && (us1.zip us2).all (fun (u, v) => univEq u v)
  | .var i _ _, .var j _ _ => return i == j
  | .prj id1 f1 v1 _, .prj id2 f2 v2 _ =>
    if id1.addr != id2.addr || f1 != f2 then
      return false
    lazyDeltaProjReduction id1 f1 v1 v2
  | _, _ => return false

partial def lazyDeltaProjReduction (structId : KId m) (field : UInt64)
    (a0 b0 : KExpr m) : RecM m Bool := do
  let mut a := a0
  let mut b := b0
  let mut fuel := maxWhnfFuel
  repeat
    if fuel == 0 then
      throw .maxRecDepth
    fuel := fuel - 1
    let (step, a', b') ← lazyDeltaReductionStep a b
    a := a'
    b := b'
    match step with
    | .equal => return true
    | .continue' => continue
    | .unknown =>
      let pa ← tryProjReduce structId field a
      let pb ← tryProjReduce structId field b
      match pa, pb with
      | some pa, some pb => return (← isDefEq pa pb)
      | _, _ => return (← isDefEq a b)
  return false

partial def lazyDeltaReductionStep (a0 b0 : KExpr m) :
    RecM m (LazyDeltaStep × KExpr m × KExpr m) := do
  let mut a := a0
  let mut b := b0
  let aHead := headConstId a
  let bHead := headConstId b
  let aDelta ← match aHead with
    | some h => isDelta h
    | none => pure false
  let bDelta ← match bHead with
    | some h => isDelta h
    | none => pure false
  if !aDelta && !bDelta then
    return (.unknown, a, b)
  if aDelta && !bDelta then
    match (← tryUnfoldProjApp b) with
    | some b2 => b := b2
    | none =>
      match (← deltaUnfoldOne a) with
      | some a2 => a ← whnfCore a2
      | none => return (.unknown, a, b)
  else if !aDelta && bDelta then
    match (← tryUnfoldProjApp a) with
    | some a2 => a := a2
    | none =>
      match (← deltaUnfoldOne b) with
      | some b2 => b ← whnfCore b2
      | none => return (.unknown, a, b)
  else
    let aId := aHead.get!
    let bId := bHead.get!
    let cmp := compareRank (← defRankId aId) (← defRankId bId)
    if cmp == .gt then
      match (← deltaUnfoldOne a) with
      | some a2 => a ← whnfCore a2
      | none => return (.unknown, a, b)
    else if cmp == .lt then
      match (← deltaUnfoldOne b) with
      | some b2 => b ← whnfCore b2
      | none => return (.unknown, a, b)
    else
      if aId.addr == bId.addr && (← isRegular aId) then
        if let some true ← trySameHeadSpine a b then
          return (.equal, a, b)
      let a2 ← deltaUnfoldOne a
      let b2 ← deltaUnfoldOne b
      match a2, b2 with
      | some a2, some b2 =>
        a ← whnfCore a2
        b ← whnfCore b2
      | some a2, none =>
        a ← whnfCore a2
      | none, some b2 =>
        b ← whnfCore b2
      | none, none => return (.unknown, a, b)
  if a.addr == b.addr || (← quickDefEq a b) then
    return (.equal, a, b)
  return (.continue', a, b)

/-- Head-Prj: one whnf-no-delta attempt (tryUnfoldProjApp). -/
partial def tryUnfoldProjApp (e : KExpr m) : RecM m (Option (KExpr m)) := do
  let (head, _) := e.collectSpine
  match head with
  | .prj .. => pure ()
  | _ => return none
  let reduced ← whnfNoDelta e
  if reduced.addr == e.addr then
    return none
  return some reduced

end

end RecM

end Ix.Tc

end
end
