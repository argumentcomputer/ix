module

public import Ix.Tc.Knot

/-!
Mirror: crates/kernel/src/inductive.rs (validation half — P8)

Inductive schema validation:
- S3/S3b: mutual peers must share the result universe, parameter count, and
  parameter-domain types (memoized per block via `blockPeerAgreementCache` —
  peer agreement is transitive, so one successful pass covers the block).
- A1: constructor parameter domains agree with the inductive's.
- A2: constructor return type is a *manifest* application of the inductive
  (no whnf at the return-type check — `id I` must not pass), with universe
  args exactly `param 0 … param (lvls-1)`, the first `n_params` args exactly
  the opened parameter fvars (FVar identity), arg count exactly
  `params + indices`, and index args free of block inductives.
- A3: strict positivity (skipped for unsafe inductives), including the
  nested-inductive rule: an external inductive applied to block-mentioning
  parameters recursively checks that external ctor fields are positive in
  the augmented address set; index args must not mention the block.
- A4: field sort levels ≤ the inductive's result level (skipped for Prop).

Also hosted here (check.rs helpers used by both dispatch and validation):
well-scopedness validation, plus `getResultSortLevel`, `isLargeEliminator`,
and `computeKTarget` (P9's recursor machinery consumes the latter two).

The recursor-generation trigger at the end of Rust's
`check_inductive_member` is deferred to P9 (`Ix.Tc.Check` will wire
`generateBlockRecursors` back in when it exists).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashSet)

namespace RecM

mutual

-- ### Well-scopedness validation (check.rs)

/-- Universe params in range, iterative with an addr-keyed seen set. -/
partial def validateUnivParamsSeen (root : KUniv m) (bound : Nat)
    (seen : HashSet Address) : RecM m (HashSet Address) := do
  let mut seen := seen
  let mut stack : Array (KUniv m) := #[root]
  while !stack.isEmpty do
    let u := stack.back!
    stack := stack.pop
    if seen.contains u.addr then
      continue
    seen := seen.insert u.addr
    match u with
    | .zero _ => pure ()
    | .succ inner _ => stack := stack.push inner
    | .max a b _ | .imax a b _ =>
      stack := stack.push a |>.push b
    | .param idx _ _ =>
      if idx.toNat ≥ bound then
        throw (.univParamOutOfRange idx bound)
  return seen

/-- Closed at top level; every `param` within the declaration's own level
    arity; const arities match; prj heads known. Iterative, memoized on
    `(addr, depth)`. Mirrors check.rs `validate_expr_well_scoped`. -/
partial def validateExprWellScoped (root : KExpr m) (rootDepth : UInt64)
    (lvlBound : Nat) : RecM m Unit := do
  let mut stack : Array (KExpr m × UInt64) := #[(root, rootDepth)]
  let mut seenExprs : HashSet (Address × UInt64) := {}
  let mut seenUnivs : HashSet Address := {}
  while !stack.isEmpty do
    let (e, depth) := stack.back!
    stack := stack.pop
    if seenExprs.contains (e.addr, depth) then
      continue
    seenExprs := seenExprs.insert (e.addr, depth)
    match e with
    | .var idx _ _ =>
      if idx ≥ depth then
        throw (.varOutOfRange idx depth.toNat)
    | .sort u _ =>
      seenUnivs ← validateUnivParamsSeen u lvlBound seenUnivs
    | .const id us _ =>
      let c ← TcM.getConst id
      if c.lvls.toNat != us.size then
        throw (.univParamMismatch c.lvls us.size)
      for u in us do
        seenUnivs ← validateUnivParamsSeen u lvlBound seenUnivs
    | .app f a _ =>
      stack := stack.push (f, depth) |>.push (a, depth)
    | .lam _ _ ty body _ | .all _ _ ty body _ =>
      stack := stack.push (ty, depth) |>.push (body, depth + 1)
    | .letE _ ty val body _ _ =>
      stack := stack.push (ty, depth) |>.push (val, depth)
        |>.push (body, depth + 1)
    | .prj id _ val _ =>
      if !(← TcM.hasConst id) then
        throw (.unknownConst id.addr)
      stack := stack.push (val, depth)
    -- FVars carry no de Bruijn index; leaves.
    | .fvar .. | .nat .. | .str .. => pure ()

partial def validateConstWellScoped (c : KConst m) : RecM m Unit := do
  let lvlBound := c.lvls.toNat
  validateExprWellScoped c.ty 0 lvlBound
  match c with
  | .defn (val := val) .. =>
    validateExprWellScoped val 0 lvlBound
  | .recr (rules := rules) .. =>
    for rule in rules do
      validateExprWellScoped rule.rhs 0 lvlBound
  | _ => pure ()

-- ### Sort/eliminator analysis

/-- Result sort after peeling `n` foralls (opened with fresh fvars). -/
partial def getResultSortLevel (ty : KExpr m) (n : Nat) :
    RecM m (KUniv m) := do
  let saved := (← get).lctx.size
  let mut t := ty
  for i in [0:n] do
    let w ← whnf t
    match w with
    | .all _ _ dom body _ =>
      let (open', _) ← TcM.openBinderAnon dom body
      t := open'
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other s!"get_result_sort_level: expected {n} foralls, only found {i}")
  let w ← whnf t
  let result ← match w with
    | .sort u _ => pure u
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "get_result_sort_level: not a sort")
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return result

/-- Large eliminator (can target any universe): non-Prop, or Empty-like
    (0 ctors), or single-ctor Prop whose non-Prop fields all appear among
    the return-type args (lean4lean `isLargeEliminator`). -/
partial def isLargeEliminator (resultLevel : KUniv m)
    (indInfos : Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m)) :
    RecM m Bool := do
  -- isNeverZero (not !isZero) so Param(u) falls through to the check below.
  if resultLevel.isNeverZero then
    return true
  if indInfos.size != 1 then
    return false
  let (_, nParams64, _, ctors, _) := indInfos[0]!
  let nParams := nParams64.toNat
  match ctors.size with
  | 0 => return true
  | 1 =>
    let (ctorTy, ctorFields) ← match (← TcM.tryGetConst ctors[0]!) with
      | some (.ctor (ty := ty) (fields := fields) ..) =>
        pure (ty, fields.toNat)
      | _ => return false
    if ctorFields == 0 then
      return true
    let saved := (← get).lctx.size
    let mut ty := ctorTy
    let mut nonTrivial : Array Nat := #[]
    let mut fieldFVars : Array (KExpr m) := Array.mkEmpty ctorFields
    for i in [0:nParams + ctorFields] do
      let w ← whnf ty
      match w with
      | .all _ _ dom body _ =>
        if i ≥ nParams then
          let domTy ← TcM.withInferOnly ((← read).infer dom)
          match (← try? (ensureSortDirect domTy)) with
          | some sortLvl =>
            if !univEq sortLvl .mkZero then
              nonTrivial := nonTrivial.push (i - nParams)
          | none => pure ()
        let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
        if i ≥ nParams then
          fieldFVars := fieldFVars.push fv
        ty := open'
      | _ => break
    let (_, retArgs) := ty.collectSpine
    let result := nonTrivial.all fun fi =>
      let target := fieldFVars[fi]!
      retArgs.any fun arg =>
        match arg with
        | .fvar .. => arg.addr == target.addr
        | _ => false
    modify fun s => { s with lctx := s.lctx.truncate saved }
    return result
  | _ => return false

/-- K-like target: single non-mutual inductive, Prop result (semantic zero),
    exactly one constructor with zero non-param fields. -/
partial def computeKTarget (indId : KId m) : RecM m Bool := do
  let (indParams, indIndices, ctors, block, ty) ←
    match (← TcM.tryGetConst indId) with
    | some (.indc (params := params) (indices := indices) (ctors := ctors)
        (block := block) (ty := ty) ..) =>
      pure (params, indices, ctors, block, ty)
    | _ => return false
  let blockInds ← discoverBlockInductives block
  if blockInds.size != 1 then
    return false
  let resultLevel ← getResultSortLevel ty (indParams + indIndices).toNat
  if !univEq resultLevel .mkZero then
    return false
  if ctors.size != 1 then
    return false
  match (← TcM.tryGetConst ctors[0]!) with
  | some (.ctor (fields := fields) ..) => return fields == 0
  | _ => return false

-- ### A1–A4 constructor validation

/-- A1 / S3b: walk the first `nParams` foralls of both types, def-eq the
    domains, and open both bodies with the SAME fvar. -/
partial def checkParamAgreement (indTy ctorTy : KExpr m) (nParams : Nat) :
    RecM m Unit := do
  let saved := (← get).lctx.size
  let mut it := indTy
  let mut ct := ctorTy
  for _ in [0:nParams] do
    let wi ← whnf it
    let wc ← whnf ct
    match wi, wc with
    | .all _ _ iDom iBody _, .all _ _ cDom cBody _ =>
      if !(← isDefEq iDom cDom) then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "param domain mismatch")
      let (iOpen, fv, _) ← TcM.openBinderAnonWithFV iDom iBody
      let cOpen ← TcM.runIntern (instantiateRev cBody #[fv])
      it := iOpen
      ct := cOpen
    | _, _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "expected forall in param agreement")
  modify fun s => { s with lctx := s.lctx.truncate saved }

/-- A3: strict positivity — block inductives must not appear in negative
    position in any constructor field. -/
partial def checkPositivity (ctorTy : KExpr m) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Unit := do
  let mut ty := ctorTy
  for _ in [0:nParams] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => ty := body
    | _ => return ()
  repeat
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      checkPositivityDomain dom blockAddrs
      ty := body
    | _ => break

/-- Field-domain positivity: recurse through foralls (negative-position
    mentions reject), then require either a direct block-inductive
    application or a valid nested-inductive application (recursively
    checked with the augmented address set). -/
partial def checkPositivityDomain (dom : KExpr m)
    (blockAddrs : Array Address) : RecM m Unit := do
  if !exprMentionsAnyAddr dom blockAddrs then
    return ()
  let w ← whnf dom
  match w with
  | .all _ _ innerDom innerBody _ =>
    -- Inductive in the domain of a Pi = negative position.
    if exprMentionsAnyAddr innerDom blockAddrs then
      throw (.other "strict positivity violation")
    -- H4: open with an fvar so whnf works on dependent types.
    let saved := (← get).lctx.size
    let (innerOpen, _) ← TcM.openBinderAnon innerDom innerBody
    let result ←
      try
        checkPositivityDomain innerOpen blockAddrs
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
    modify fun s => { s with lctx := s.lctx.truncate saved }
    match result with
    | .ok () => return ()
    | .error e => throw e
  | _ =>
    let (head, args) := w.collectSpine
    match head with
    | .const id us _ =>
      if blockAddrs.contains id.addr then
        return ()
      -- Nested inductive: external inductive whose params mention the block.
      let (nParams, block, ctors) ← match (← TcM.getConst id) with
        | .indc (params := params) (block := block) (ctors := ctors) .. =>
          pure (params.toNat, block, ctors)
        | _ => throw (.other "positivity: not a valid inductive app")
      let hasNestedRef := (args.extract 0 (min nParams args.size)).any
        (exprMentionsAnyAddr · blockAddrs)
      if !hasNestedRef then
        throw (.other "positivity: not a valid inductive app")
      -- Index args (after params) must not mention block inductives.
      for arg in args.extract nParams args.size do
        if exprMentionsAnyAddr arg blockAddrs then
          throw (.other "positivity: index mentions block inductive")
      -- Augmented address set: block + the external inductive's block.
      let mut augmented := blockAddrs
      for extId in (← discoverBlockInductives block) do
        if !augmented.contains extId.addr then
          augmented := augmented.push extId.addr
      let paramArgs := args.extract 0 (min nParams args.size)
      for ctorId in ctors do
        let ctorTy ← match (← TcM.getConst ctorId) with
          | .ctor (ty := ty) .. => pure ty
          | _ => throw (.other "positivity: nested ctor not found")
        checkNestedCtorFields ctorTy nParams paramArgs us augmented
    | _ => throw (.other "positivity: not a valid inductive app")

/-- Nested-inductive field positivity: instantiate universes, strip the
    external inductive's param binders, simultaneously substitute the
    actual (block-mentioning) parameter arguments, then check each
    remaining field domain against the augmented address set. -/
partial def checkNestedCtorFields (ctorTy : KExpr m) (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (augmentedAddrs : Array Address) : RecM m Unit := do
  let mut ty ← TcM.instantiateUnivParams ctorTy us
  for _ in [0:nParams] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => ty := body
    | _ => return ()
  -- Var(0) = innermost = LAST param after stripping; simulSubst maps
  -- Var(i) ↦ substs[i], so reverse the param order.
  ty ← TcM.runIntern (simulSubst ty paramArgs.reverse 0)
  checkNestedCtorFieldsLoop ty augmentedAddrs

partial def checkNestedCtorFieldsLoop (ty : KExpr m)
    (augmentedAddrs : Array Address) : RecM m Unit := do
  let w ← whnf ty
  match w with
  | .all _ _ dom body _ =>
    checkPositivityDomain dom augmentedAddrs
    let saved := (← get).lctx.size
    let (open', _) ← TcM.openBinderAnon dom body
    let result ←
      try
        checkNestedCtorFieldsLoop open' augmentedAddrs
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
    modify fun s => { s with lctx := s.lctx.truncate saved }
    match result with
    | .ok () => return ()
    | .error e => throw e
  | _ => return ()

/-- A4: field sort levels ≤ the inductive's result level (Prop inductives
    are exempt). -/
partial def checkFieldUniverses (ctorTy : KExpr m) (nParams : Nat)
    (indLevel : KUniv m) : RecM m Unit := do
  if indLevel.isZero then
    return ()
  let saved := (← get).lctx.size
  let mut ty := ctorTy
  for _ in [0:nParams] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (open', _) ← TcM.openBinderAnon dom body
      ty := open'
    | _ => break
  repeat
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let domTy ← infer dom
      let fieldLevel ← ensureSortDirect domTy
      if !univGeq indLevel fieldLevel then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "field universe exceeds inductive level")
      let (open', _) ← TcM.openBinderAnon dom body
      ty := open'
    | _ => break
  modify fun s => { s with lctx := s.lctx.truncate saved }

/-- A2: constructor return type (see module doc for the exact conditions). -/
partial def checkCtorReturnType (ctorTy : KExpr m)
    (nParams nIndices nFields : Nat) (indAddr : Address) (indLvls : UInt64)
    (blockAddrs : Array Address) : RecM m Unit := do
  let saved := (← get).lctx.size
  let mut ty := ctorTy
  let totalBinders := nParams + nFields
  let mut paramFVars : Array (KExpr m) := Array.mkEmpty nParams
  for i in [0:totalBinders] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
      if i < nParams then
        paramFVars := paramFVars.push fv
      ty := open'
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: not enough binders")
  -- Do NOT whnf: the return type must be a *manifest* `I args…`.
  let (head, args) := ty.collectSpine
  match head with
  | .const id us _ =>
    if id.addr != indAddr then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: head is not the inductive")
    if us.size.toUInt64 != indLvls then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other s!"ctor return type: expected {indLvls} universe args, got {us.size}")
    for i in [0:us.size] do
      let expected : KUniv m := .mkParam i.toUInt64 anonN
      if !univEq us[i]! expected then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other s!"ctor return type: universe arg {i} is not Param({i})")
  | _ =>
    modify fun s => { s with lctx := s.lctx.truncate saved }
    throw (.other "ctor return type: head is not the inductive")
  -- S2: exact arg count.
  if args.size != nParams + nIndices then
    modify fun s => { s with lctx := s.lctx.truncate saved }
    throw (.other s!"ctor return type: expected {nParams + nIndices} args (params={nParams} + indices={nIndices}), got {args.size}")
  -- First nParams args are exactly the param fvars.
  for i in [0:nParams] do
    match args[i]? with
    | none =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: not enough args for params")
    | some arg =>
      if arg.addr != paramFVars[i]!.addr then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "ctor return type: param arg not the param fvar")
  -- Index args must not mention block inductives.
  for arg in args.extract nParams args.size do
    if exprMentionsAnyAddr arg blockAddrs then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: index mentions block inductive")
  modify fun s => { s with lctx := s.lctx.truncate saved }

-- ### Member / block validation

/-- Validate an inductive and every one of its constructors (S3/S3b peer
    agreement + A1–A4). The Rust tail (recursor-generation trigger) lands
    with P9. -/
partial def checkInductiveMemberImpl (id : KId m) : RecM m Unit := do
  let (params, indices, lvls, ctors, block, isUnsafe, ty) ←
    match (← TcM.getConst id) with
    | .indc (params := params) (indices := indices) (lvls := lvls)
        (ctors := ctors) (block := block) (isUnsafe := isUnsafe)
        (ty := ty) .. =>
      pure (params, indices, lvls, ctors, block, isUnsafe, ty)
    | _ => throw (.other "check_inductive: not an inductive")
  let blockInds ← discoverBlockInductives block
  let blockAddrs := blockInds.map (·.addr)
  -- Result sort must exist even for ctor-less inductives.
  let indLevel ← getResultSortLevel ty (params + indices).toNat
  -- S3/S3b, memoized per block (transitive agreement).
  if !(← get).env.blockPeerAgreementCache.contains block then
    for peerId in blockInds do
      if peerId.addr == id.addr then
        continue
      let (peerParams, peerIndices, peerTy) ← match (← TcM.getConst peerId) with
        | .indc (params := pp) (indices := pi) (ty := pty) .. =>
          pure (pp, pi, pty)
        | _ => continue
      let peerLevel ← getResultSortLevel peerTy (peerParams + peerIndices).toNat
      if !univEq indLevel peerLevel then
        throw (.other "mutually inductive types must live in the same universe")
      if peerParams != params then
        throw (.other s!"mutual peers must declare the same number of parameters: self={params}, peer={peerParams}")
      checkParamAgreement ty peerTy params.toNat
    modify fun s => { s with env := { s.env with
      blockPeerAgreementCache := s.env.blockPeerAgreementCache.insert block } }
  -- Per-constructor A1–A4.
  for h : expectedCidx in [0:ctors.size] do
    let ctorId := ctors[expectedCidx]
    let (ctorParams, ctorFields, ctorCidx, ctorTy) ←
      match (← TcM.getConst ctorId) with
      | .ctor (params := cp) (fields := cf) (cidx := cc) (ty := cty) .. =>
        pure (cp.toNat, cf.toNat, cc.toNat, cty)
      | _ => throw (.other "check_inductive: constructor not found")
    if ctorParams != params.toNat then
      throw (.other s!"check_inductive: ctor params mismatch: expected {params.toNat}, got {ctorParams}")
    if ctorCidx != expectedCidx then
      throw (.other s!"check_inductive: ctor cidx mismatch: expected {expectedCidx}, got {ctorCidx}")
    checkParamAgreement ty ctorTy params.toNat
    if !isUnsafe then
      checkPositivity ctorTy params.toNat blockAddrs
    checkFieldUniverses ctorTy params.toNat indLevel
    checkCtorReturnType ctorTy params.toNat indices.toNat ctorFields
      id.addr lvls blockAddrs
  -- TODO(P9): trigger generateBlockRecursors for the block here (fatal on
  -- failure), matching check_inductive_member's tail.

/-- Standalone-constructor validation: the same per-ctor A1–A4 against the
    declared parent. -/
partial def checkCtorAgainstInductiveMemberImpl (ctorId inductId : KId m) :
    RecM m Unit := do
  let (ctorTy, ctorFields) ← match (← TcM.getConst ctorId) with
    | .ctor (ty := ty) (fields := fields) .. => pure (ty, fields.toNat)
    | _ => throw (.other "check_ctor: not a constructor")
  let (indParams, indIndices, indLvls, indBlock, indIsUnsafe, indTy) ←
    match (← TcM.getConst inductId) with
    | .indc (params := params) (indices := indices) (lvls := lvls)
        (block := block) (isUnsafe := isUnsafe) (ty := ty) .. =>
      pure (params, indices, lvls, block, isUnsafe, ty)
    | _ => throw (.other "check_ctor: parent inductive not found")
  let blockInds ← discoverBlockInductives indBlock
  let blockAddrs := blockInds.map (·.addr)
  let indLevel ← getResultSortLevel indTy (indParams + indIndices).toNat
  checkParamAgreement indTy ctorTy indParams.toNat
  if !indIsUnsafe then
    checkPositivity ctorTy indParams.toNat blockAddrs
  checkFieldUniverses ctorTy indParams.toNat indLevel
  checkCtorReturnType ctorTy indParams.toNat indIndices.toNat ctorFields
    inductId.addr indLvls blockAddrs

/-- Validate every inductive and constructor of a homogeneous inductive
    block: per-member well-scopedness + type inference, then the member
    checks. -/
partial def checkInductiveBlockImpl (block : KId m) (members : Array (KId m)) :
    RecM m Unit := do
  let mut indIds : Array (KId m) := #[]
  let mut ctorIds : Array (KId m) := #[]
  for member in members do
    TcM.reset (m := m)
    let c ← TcM.getConst member
    validateConstWellScoped c
    match c with
    | .indc (ty := ty) .. =>
      let t ← infer ty
      let _ ← ensureSortDirect t
      indIds := indIds.push member
    | .ctor (ty := ty) .. =>
      let t ← infer ty
      let _ ← ensureSortDirect t
      ctorIds := ctorIds.push member
    | _ =>
      throw (.other s!"check_inductive_block: non-inductive member {member} in block {block}")
  for indId in indIds do
    TcM.reset (m := m)
    checkInductiveMemberImpl indId
  for ctorId in ctorIds do
    let induct ← match (← TcM.getConst ctorId) with
      | .ctor (induct := induct) .. => pure induct
      | _ => continue
    TcM.reset (m := m)
    checkCtorAgainstInductiveMemberImpl ctorId induct

end

end RecM

end Ix.Tc

end
end
