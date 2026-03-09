/-
  Kernel2 Infer: Krivine machine with call-by-need thunks.

  Mutual block: eval, applyValThunk, forceThunk, whnfCoreVal, deltaStepVal,
  whnfVal, tryIotaReduction, tryQuotReduction, isDefEq, isDefEqCore,
  isDefEqSpine, lazyDelta, unfoldOneDelta, quote.

  Key changes from substitution-based kernel:
  - Spine args are ThunkIds (lazy, memoized via ST.Ref)
  - Beta reduction is O(1) via closures
  - Delta unfolding is single-step (Krivine semantics)
  - isDefEq works entirely on Val (no quoting)
-/
import Ix.Kernel.Helpers
import Ix.Kernel.Quote
import Ix.Kernel.Primitive
import Ix.Kernel.ExprUtils

namespace Ix.Kernel

-- Uses K-abbreviations from Value.lean to avoid Lean.* shadowing

/-! ## Pointer equality helper -/

private unsafe def ptrEqUnsafe (a : @& Val m) (b : @& Val m) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[implemented_by ptrEqUnsafe]
private opaque ptrEq : @& Val m → @& Val m → Bool

private unsafe def ptrAddrValUnsafe (a : @& Val m) : USize := ptrAddrUnsafe a

@[implemented_by ptrAddrValUnsafe]
private opaque ptrAddrVal : @& Val m → USize

private unsafe def arrayPtrEqUnsafe (a : @& Array (Val m)) (b : @& Array (Val m)) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[implemented_by arrayPtrEqUnsafe]
private opaque arrayPtrEq : @& Array (Val m) → @& Array (Val m) → Bool

private unsafe def arrayValPtrEqUnsafe (a : @& Array (Val m)) (b : @& Array (Val m)) : Bool :=
  if a.size != b.size then false
  else Id.run do
    for i in [:a.size] do
      if ptrAddrUnsafe a[i]! != ptrAddrUnsafe b[i]! then return false
    return true

@[implemented_by arrayValPtrEqUnsafe]
private opaque arrayValPtrEq : @& Array (Val m) → @& Array (Val m) → Bool

/-- Check universe array equality. -/
private def equalUnivArrays (us vs : Array (KLevel m)) : Bool :=
  if us.size != vs.size then false
  else Id.run do
    for i in [:us.size] do
      if !Ix.Kernel.Level.equalLevel us[i]! vs[i]! then return false
    return true

private def isBoolTrue (prims : KPrimitives) (v : Val m) : Bool :=
  match v with
  | .neutral (.const addr _ _) spine => addr == prims.boolTrue && spine.isEmpty
  | .ctor addr _ _ _ _ _ _ spine => addr == prims.boolTrue && spine.isEmpty
  | _ => false

/-! ## Mutual block -/

mutual
  /-- Evaluate an Expr in an environment to produce a Val.
      App arguments become thunks (lazy). Constants stay as stuck neutrals. -/
  partial def eval (e : KExpr m) (env : Array (Val m)) : TypecheckM σ m (Val m) := do
    heartbeat
    match e with
    | .bvar idx _ =>
      let envSize := env.size
      if idx < envSize then
        pure env[envSize - 1 - idx]!
      else
        let ctx ← read
        let ctxIdx := idx - envSize
        let ctxDepth := ctx.types.size
        if ctxIdx < ctxDepth then
          let level := ctxDepth - 1 - ctxIdx
          if h : level < ctx.letValues.size then
            if let some val := ctx.letValues[level] then
              return val  -- zeta-reduce let-bound variable
          if h2 : level < ctx.types.size then
            return Val.mkFVar level ctx.types[level]
          else
            throw s!"bvar {idx} out of bounds (env={envSize}, ctx={ctxDepth})"
        else
          let envStrs := env.map (fun v => Val.pp v)
          throw s!"bvar {idx} out of bounds (env={envSize}, ctx={ctxDepth}) envVals={envStrs}"

    | .sort lvl => pure (.sort lvl)

    | .const addr levels name =>
      let kenv := (← read).kenv
      match kenv.find? addr with
      | some (.ctorInfo cv) =>
        pure (.ctor addr levels name cv.cidx cv.numParams cv.numFields cv.induct #[])
      | _ => pure (Val.neutral (.const addr levels name) #[])

    | .app .. => do
      let args := e.getAppArgs
      let fn := e.getAppFn
      let mut fnV ← eval fn env
      for arg in args do
        match fnV with
        | .lam _ _ _ body lamEnv =>
          -- Head is lambda: eager arg eval, direct beta (skip thunk allocation)
          let argV ← eval arg env
          fnV ← eval body (lamEnv.push argV)
        | _ =>
          -- Head is not lambda: create thunk (lazy)
          let thunkId ← mkThunk arg env
          fnV ← applyValThunk fnV thunkId
      pure fnV

    | .lam ty body name bi => do
      let domV ← eval ty env
      pure (.lam name bi domV body env)

    | .forallE ty body name bi => do
      let domV ← eval ty env
      pure (.pi name bi domV body env)

    | .letE _ty val body _name => do
      let valV ← eval val env
      eval body (env.push valV)

    | .lit l => pure (.lit l)

    | .proj typeAddr idx struct typeName => do
      -- Eval struct directly; only create thunk if projection is stuck
      let structV ← eval struct env
      let kenv := (← read).kenv
      let prims := (← read).prims
      match reduceValProjForced typeAddr idx structV kenv prims with
      | some fieldThunkId => forceThunk fieldThunkId
      | none =>
        let structThunkId ← mkThunkFromVal structV
        pure (.proj typeAddr idx structThunkId typeName #[])

  /-- Evaluate an Expr with context bvars pre-resolved to fvars in the env.
      This makes closures context-independent: their envs capture fvars
      instead of relying on context fallthrough for bvar resolution. -/
  partial def evalInCtx (e : KExpr m) : TypecheckM σ m (Val m) := do
    let ctx ← read
    let ctxDepth := ctx.types.size
    if ctxDepth == 0 then eval e #[]
    else
      let mut env : Array (Val m) := Array.mkEmpty ctxDepth
      for level in [:ctxDepth] do
        if h : level < ctx.letValues.size then
          if let some val := ctx.letValues[level] then
            env := env.push val
            continue
        if h2 : level < ctx.types.size then
          env := env.push (Val.mkFVar level ctx.types[level])
        else unreachable!
      eval e env

  /-- Apply a value to a thunked argument. O(1) beta for lambdas. -/
  partial def applyValThunk (fn : Val m) (argThunkId : Nat)
      : TypecheckM σ m (Val m) := do
    heartbeat
    match fn with
    | .lam _name _ _ body env =>
      -- Force the thunk to get the value, push onto closure env
      let argV ← forceThunk argThunkId
      try eval body (env.push argV)
      catch e => throw s!"in apply-lam({_name}) [env={env.size}→{env.size+1}, body={body.tag}]: {e}"
    | .neutral head spine =>
      -- Accumulate thunk on spine (LAZY — not forced!)
      pure (.neutral head (spine.push argThunkId))
    | .ctor addr levels name cidx numParams numFields inductAddr spine =>
      -- Accumulate thunk on ctor spine (LAZY — not forced!)
      pure (.ctor addr levels name cidx numParams numFields inductAddr (spine.push argThunkId))
    | .proj typeAddr idx structThunkId typeName spine => do
      -- Try whnf on the struct to reduce the projection
      let structV ← forceThunk structThunkId
      let structV' ← whnfVal structV
      let kenv := (← read).kenv
      let prims := (← read).prims
      match reduceValProjForced typeAddr idx structV' kenv prims with
      | some fieldThunkId =>
        let fieldV ← forceThunk fieldThunkId
        -- Apply accumulated spine args first, then the new arg
        let mut result := fieldV
        for tid in spine do
          result ← applyValThunk result tid
        applyValThunk result argThunkId
      | none =>
        -- Projection still stuck — accumulate arg on spine
        pure (.proj typeAddr idx structThunkId typeName (spine.push argThunkId))
    | _ => throw s!"cannot apply non-function value"

  /-- Force a thunk: if unevaluated, eval and memoize; if evaluated, return cached. -/
  partial def forceThunk (id : Nat) : TypecheckM σ m (Val m) := do
    let tableRef := (← read).thunkTable
    let table ← ST.Ref.get tableRef
    if h : id < table.size then
      let entryRef := table[id]
      let entry ← ST.Ref.get entryRef
      match entry with
      | .evaluated val =>
        pure val
      | .unevaluated expr env =>
        heartbeat
        let val ← eval expr env
        ST.Ref.set entryRef (.evaluated val)
        pure val
    else
      throw s!"thunk id {id} out of bounds (table size {table.size})"

  /-- Iota-reduction: reduce a recursor applied to a constructor. -/
  partial def tryIotaReduction (_addr : Address) (levels : Array (KLevel m))
      (spine : Array Nat) (params motives minors indices : Nat)
      (rules : Array (Nat × KTypedExpr m)) : TypecheckM σ m (Option (Val m)) := do
    let majorIdx := params + motives + minors + indices
    if majorIdx >= spine.size then return none
    let major ← forceThunk spine[majorIdx]!
    let major' ← whnfVal major
    -- Convert nat literal to constructor form (0 → Nat.zero, n+1 → Nat.succ)
    let major'' ← match major' with
      | .lit (.natVal _) => natLitToCtorThunked major'
      | v => pure v
    -- Check if major is a constructor
    match major'' with
    | .ctor _ _ _ ctorIdx numParams _ _ ctorSpine =>
      match rules[ctorIdx]? with
      | some (nfields, rhs) =>
        if nfields > ctorSpine.size then return none
        let rhsBody := rhs.body.instantiateLevelParams levels
        let mut result ← eval rhsBody #[]
        -- Apply params + motives + minors from rec spine
        let pmmEnd := params + motives + minors
        for i in [:pmmEnd] do
          if i < spine.size then
            result ← applyValThunk result spine[i]!
        -- Apply constructor fields (skip constructor params)
        let ctorParamCount := numParams
        for i in [ctorParamCount:ctorSpine.size] do
          result ← applyValThunk result ctorSpine[i]!
        -- Apply extra args after major premise
        if majorIdx + 1 < spine.size then
          for i in [majorIdx + 1:spine.size] do
            result ← applyValThunk result spine[i]!
        return some result
      | none => return none
    | _ => return none

  /-- For K-like inductives, verify the major's type matches the inductive.
      Returns the constructed ctor (not needed for K-reduction itself, just validation). -/
  partial def toCtorWhenKVal (major : Val m) (indAddr : Address)
      : TypecheckM σ m (Option (Val m)) := do
    let kenv := (← read).kenv
    match kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if iv.ctors.isEmpty then return none
      let ctorAddr := iv.ctors[0]!
      let majorType ← try inferTypeOfVal major catch e =>
        if (← read).trace then dbg_trace s!"toCtorWhenKVal: inferTypeOfVal(major) threw: {e}"
        return none
      let majorType' ← whnfVal majorType
      match majorType' with
      | .neutral (.const headAddr univs _) typeSpine =>
        if headAddr != indAddr then return none
        -- Build the nullary ctor applied to params from the type
        let mut ctorArgs : Array Nat := #[]
        for i in [:iv.numParams] do
          if i < typeSpine.size then
            ctorArgs := ctorArgs.push typeSpine[i]!
        -- Look up ctor info to build Val.ctor
        match kenv.find? ctorAddr with
        | some (.ctorInfo cv) =>
          let ctorVal := Val.ctor ctorAddr univs default cv.cidx cv.numParams cv.numFields cv.induct ctorArgs
          -- Verify ctor type matches major type
          let ctorType ← try inferTypeOfVal ctorVal catch e =>
            if (← read).trace then dbg_trace s!"toCtorWhenKVal: inferTypeOfVal(ctor) threw: {e}"
            return none
          if !(← isDefEq majorType ctorType) then return none
          return some ctorVal
        | _ => return none
      | _ => return none
    | _ => return none

  /-- K-reduction: for K-recursors (Prop, single zero-field ctor).
      Returns the minor premise directly, without needing the major to be a constructor. -/
  partial def tryKReductionVal (_levels : Array (KLevel m)) (spine : Array Nat)
      (params motives minors indices : Nat) (indAddr : Address)
      (_rules : Array (Nat × KTypedExpr m)) : TypecheckM σ m (Option (Val m)) := do
    let majorIdx := params + motives + minors + indices
    if majorIdx >= spine.size then return none
    let major ← forceThunk spine[majorIdx]!
    let major' ← whnfVal major
    -- Check if major is already a constructor
    let isCtor := match major' with
      | .ctor .. => true
      | _ => false
    if !isCtor then
      -- Verify major's type matches the K-inductive
      match ← toCtorWhenKVal major' indAddr with
      | some _ => pure ()  -- type matches, proceed with K-reduction
      | none => return none
    -- K-reduction: return the minor premise
    let minorIdx := params + motives
    if minorIdx >= spine.size then return none
    let minor ← forceThunk spine[minorIdx]!
    let mut result := minor
    -- Apply extra args after major
    if majorIdx + 1 < spine.size then
      for i in [majorIdx + 1:spine.size] do
        result ← applyValThunk result spine[i]!
    return some result

  /-- Structure eta in iota: when major isn't a ctor but inductive is structure-like,
      eta-expand via projections. Skips Prop structures. -/
  partial def tryStructEtaIota (levels : Array (KLevel m)) (spine : Array Nat)
      (params motives minors indices : Nat) (indAddr : Address)
      (rules : Array (Nat × KTypedExpr m)) (major : Val m)
      : TypecheckM σ m (Option (Val m)) := do
    let kenv := (← read).kenv
    if !kenv.isStructureLike indAddr then return none
    -- Skip Prop structures (proof irrelevance handles them)
    let isPropType ← try isPropVal major catch e =>
      if (← read).trace then dbg_trace s!"tryStructEtaIota: isPropVal threw: {e}"
      pure false
    if isPropType then return none
    match rules[0]? with
    | some (nfields, rhs) =>
      let rhsBody := rhs.body.instantiateLevelParams levels
      let mut result ← eval rhsBody #[]
      -- Phase 1: params + motives + minors
      let pmmEnd := params + motives + minors
      for i in [:pmmEnd] do
        if i < spine.size then
          result ← applyValThunk result spine[i]!
      -- Phase 2: projections as fields
      let majorThunkId ← mkThunkFromVal major
      for i in [:nfields] do
        let projVal := Val.proj indAddr i majorThunkId default #[]
        let projThunkId ← mkThunkFromVal projVal
        result ← applyValThunk result projThunkId
      -- Phase 3: extra args after major
      let majorIdx := params + motives + minors + indices
      if majorIdx + 1 < spine.size then
        for i in [majorIdx + 1:spine.size] do
          result ← applyValThunk result spine[i]!
      return some result
    | none => return none

  /-- Quotient reduction: Quot.lift / Quot.ind. -/
  partial def tryQuotReduction (spine : Array Nat) (reduceSize fPos : Nat)
      : TypecheckM σ m (Option (Val m)) := do
    if spine.size < reduceSize then return none
    let majorIdx := reduceSize - 1
    let major ← forceThunk spine[majorIdx]!
    let major' ← whnfVal major
    match major' with
    | .neutral (.const majorAddr _ _) majorSpine =>
      ensureTypedConst majorAddr
      match (← get).typedConsts.get? majorAddr with
      | some (.quotient _ .ctor) =>
        if majorSpine.size < 3 then throw "Quot.mk should have at least 3 args"
        let dataArgThunk := majorSpine[majorSpine.size - 1]!
        if fPos >= spine.size then return none
        let f ← forceThunk spine[fPos]!
        let mut result ← applyValThunk f dataArgThunk
        if majorIdx + 1 < spine.size then
          for i in [majorIdx + 1:spine.size] do
            result ← applyValThunk result spine[i]!
        return some result
      | _ => return none
    | _ => return none

  /-- Structural WHNF implementation: proj reduction, iota reduction. No delta. -/
  partial def whnfCoreImpl (v : Val m) (cheapRec : Bool) (cheapProj : Bool)
      : TypecheckM σ m (Val m) := do
    heartbeat
    match v with
    | .proj typeAddr idx structThunkId typeName spine => do
      -- Collect nested projection chain (outside-in)
      let mut projStack : Array (Address × Nat × KMetaField m Ix.Name × Array Nat) :=
        #[(typeAddr, idx, typeName, spine)]
      let mut innerThunkId := structThunkId
      repeat
        let innerV ← forceThunk innerThunkId
        match innerV with
        | .proj ta i st tn sp =>
          projStack := projStack.push (ta, i, tn, sp)
          innerThunkId := st
        | _ => break
      -- Reduce the innermost struct once
      let innerV ← forceThunk innerThunkId
      let innerV' ← if cheapProj then whnfCoreVal innerV cheapRec cheapProj
                     else whnfVal innerV
      -- Resolve projections from inside out (last pushed = innermost)
      let kenv := (← read).kenv
      let prims := (← read).prims
      let mut current := innerV'
      let mut i := projStack.size
      while i > 0 do
        i := i - 1
        let (ta, ix, tn, sp) := projStack[i]!
        match reduceValProjForced ta ix current kenv prims with
        | some fieldThunkId =>
          let fieldV ← forceThunk fieldThunkId
          current ← whnfCoreVal fieldV cheapRec cheapProj
          -- Apply accumulated spine args after reducing each projection
          for tid in sp do
            current ← applyValThunk current tid
            current ← whnfCoreVal current cheapRec cheapProj
        | none =>
          -- This projection couldn't be resolved. Reconstruct remaining chain.
          let mut stId ← mkThunkFromVal current
          -- Rebuild from current projection outward
          current := Val.proj ta ix stId tn sp
          while i > 0 do
            i := i - 1
            let (ta', ix', tn', sp') := projStack[i]!
            stId ← mkThunkFromVal current
            current := Val.proj ta' ix' stId tn' sp'
          return current
      pure current
    | .neutral (.const addr _ _) spine => do
      if cheapRec then return v
      -- Try iota/quot reduction — look up directly in kenv (not ensureTypedConst)
      let kenv := (← read).kenv
      match kenv.find? addr with
      | some (.recInfo rv) =>
        let levels := match v with | .neutral (.const _ ls _) _ => ls | _ => #[]
        let typedRules := rv.rules.map fun r =>
          (r.nfields, (⟨default, r.rhs⟩ : KTypedExpr m))
        let indAddr := getMajorInduct rv.toConstantVal.type rv.numParams rv.numMotives rv.numMinors rv.numIndices |>.getD default
        if rv.k then
          -- K-reduction: for Prop inductives with single zero-field ctor
          match ← tryKReductionVal levels spine rv.numParams rv.numMotives rv.numMinors rv.numIndices indAddr typedRules with
          | some result => whnfCoreVal result cheapRec cheapProj
          | none => pure v
        else
          match ← tryIotaReduction addr levels spine rv.numParams rv.numMotives rv.numMinors rv.numIndices typedRules with
          | some result => whnfCoreVal result cheapRec cheapProj
          | none =>
            -- Struct eta fallback: expand struct-like major via projections
            let majorIdx := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
            if majorIdx < spine.size then
              let major ← forceThunk spine[majorIdx]!
              let major' ← whnfVal major
              match ← tryStructEtaIota levels spine rv.numParams rv.numMotives rv.numMinors rv.numIndices indAddr typedRules major' with
              | some result => whnfCoreVal result cheapRec cheapProj
              | none => pure v
            else pure v
      | some (.quotInfo qv) =>
        match qv.kind with
        | .lift =>
          match ← tryQuotReduction spine 6 3 with
          | some result => whnfCoreVal result cheapRec cheapProj
          | none => pure v
        | .ind =>
          match ← tryQuotReduction spine 5 3 with
          | some result => whnfCoreVal result cheapRec cheapProj
          | none => pure v
        | _ => pure v
      | _ => pure v
    | _ => pure v  -- lam, pi, sort, lit, fvar-neutral: already in WHNF

  /-- Structural WHNF on Val: proj reduction, iota reduction. No delta.
      cheapProj=true: don't whnf the struct inside a projection.
      cheapRec=true: don't attempt iota reduction on recursors.
      Caches results when !cheapRec && !cheapProj (pointer-keyed). -/
  partial def whnfCoreVal (v : Val m) (cheapRec := false) (cheapProj := false)
      : TypecheckM σ m (Val m) := do
    let useCache := !cheapRec && !cheapProj
    if useCache then
      let vPtr := ptrAddrVal v
      match (← get).whnfCoreCache.get? vPtr with
      | some (inputRef, cached) =>
        if ptrEq v inputRef then
          return cached
      | none => pure ()
    let result ← whnfCoreImpl v cheapRec cheapProj
    if useCache then
      let vPtr := ptrAddrVal v
      modify fun st => { st with
        whnfCoreCache := st.whnfCoreCache.insert vPtr (v, result) }
    pure result

  /-- Single delta unfolding step. Returns none if not delta-reducible. -/
  partial def deltaStepVal (v : Val m) : TypecheckM σ m (Option (Val m)) := do
    heartbeat
    match v with
    | .neutral (.const addr levels name) spine =>
      let kenv := (← read).kenv
      match kenv.find? addr with
      | some (.defnInfo dv) =>
        let body := if dv.toConstantVal.numLevels == 0 then dv.value
          else dv.value.instantiateLevelParams levels
        let mut result ← eval body #[]
        for thunkId in spine do
          result ← applyValThunk result thunkId
        pure (some result)
      | some (.thmInfo tv) =>
        let body := if tv.toConstantVal.numLevels == 0 then tv.value
          else tv.value.instantiateLevelParams levels
        let mut result ← eval body #[]
        for thunkId in spine do
          result ← applyValThunk result thunkId
        pure (some result)
      | _ => pure none
    | _ => pure none

  /-- Try to reduce a nat primitive. Selectively forces only the args needed. -/
  partial def tryReduceNatVal (v : Val m) : TypecheckM σ m (Option (Val m)) := do
    match v with
    | .neutral (.const addr _ _) spine =>
      let prims := (← read).prims
      if !isPrimOp prims addr then return none
      if addr == prims.natSucc then
        if h : 0 < spine.size then
          let arg ← forceThunk spine[0]
          let arg' ← whnfVal arg
          match extractNatVal prims arg' with
          | some n => pure (some (.lit (.natVal (n + 1))))
          | none => pure none
        else pure none
      else if h : 1 < spine.size then
        let a ← forceThunk spine[0]
        let b ← forceThunk spine[1]
        let a' ← whnfVal a
        let b' ← whnfVal b
        match extractNatVal prims a', extractNatVal prims b' with
        | some x, some y => pure (computeNatPrim prims addr x y)
        -- Partial reduction: second arg is 0 (base cases of Nat.add/sub/mul/pow recursors)
        | _, some 0 =>
          if addr == prims.natAdd then pure (some a')                      -- n + 0 = n
          else if addr == prims.natSub then pure (some a')                 -- n - 0 = n
          else if addr == prims.natMul then pure (some (.lit (.natVal 0))) -- n * 0 = 0
          else if addr == prims.natPow then pure (some (.lit (.natVal 1))) -- n ^ 0 = 1
          else pure none
        | _, _ => pure none
      else pure none
    | _ => pure none

  /-- Try to reduce a native reduction marker (reduceBool/reduceNat).
      Shape: `neutral (const reduceBool/reduceNat []) [thunk(const targetDef [])]`.
      Looks up the target constant's definition, evaluates it, and extracts Bool/Nat. -/
  partial def reduceNativeVal (v : Val m) : TypecheckM σ m (Option (Val m)) := do
    match v with
    | .neutral (.const fnAddr _ _) spine =>
      let prims := (← read).prims
      if prims.reduceBool == default && prims.reduceNat == default then return none
      let isReduceBool := fnAddr == prims.reduceBool
      let isReduceNat := fnAddr == prims.reduceNat
      if !isReduceBool && !isReduceNat then return none
      if h : 0 < spine.size then
        let arg ← forceThunk spine[0]
        match arg with
        | .neutral (.const defAddr levels _) _ =>
          let kenv := (← read).kenv
          match kenv.find? defAddr with
          | some (.defnInfo dv) =>
            let body := if dv.toConstantVal.numLevels == 0 then dv.value
              else dv.value.instantiateLevelParams levels
            let result ← eval body #[]
            let result' ← whnfVal result
            if isReduceBool then
              if isBoolTrue prims result' then
                return some (← mkCtorVal prims.boolTrue #[] #[])
              else
                let isFalse := match result' with
                  | .neutral (.const addr _ _) sp => addr == prims.boolFalse && sp.isEmpty
                  | .ctor addr _ _ _ _ _ _ sp => addr == prims.boolFalse && sp.isEmpty
                  | _ => false
                if isFalse then
                  return some (← mkCtorVal prims.boolFalse #[] #[])
                else throw "reduceBool: constant did not reduce to Bool.true or Bool.false"
            else -- isReduceNat
              match extractNatVal prims result' with
              | some n => return some (.lit (.natVal n))
              | none => throw "reduceNat: constant did not reduce to a Nat literal"
          | _ => throw "reduceNative: target is not a definition"
        | _ => return none
      else return none
    | _ => return none

  /-- Try to fully evaluate a delta-reducible neutral by unfolding its definition
      and eagerly applying all spine args. Returns none if stuck (non-reducible neutral,
      opaque/partial, or evaluation fails). Like Kernel1's Eval.tryEvalToExpr. -/
  partial def tryEvalVal (v : Val m) (fuel : Nat := 10000) : TypecheckM σ m (Option (Val m)) := do
    if fuel == 0 then return none
    match v with
    | .neutral (.const addr levels _) spine =>
      let kenv := (← read).kenv
      let prims := (← read).prims
      -- Nat primitives: try direct computation
      if isPrimOp prims addr then
        return ← tryReduceNatVal v
      match kenv.find? addr with
      | some (.defnInfo dv) =>
        if dv.safety == .partial then return none
        let body := if dv.toConstantVal.numLevels == 0 then dv.value
          else dv.value.instantiateLevelParams levels
        let mut result ← eval body #[]
        for thunkId in spine do
          match result with
          | .lam _ _ _ lamBody lamEnv =>
            let argV ← forceThunk thunkId
            result ← eval lamBody (lamEnv.push argV)
          | _ =>
            result ← applyValThunk result thunkId
        -- Check if result is fully reduced (not a stuck neutral needing further delta)
        match result with
        | .lit .. | .ctor .. | .lam .. | .pi .. | .sort .. => return some result
        | .neutral (.const addr' _ _) _ =>
          match kenv.find? addr' with
          | some (.defnInfo _) | some (.thmInfo _) => return none  -- needs more delta, bail
          | _ => return some result  -- stuck on axiom/inductive/etc, return as-is
        | _ => return some result
      | _ => return none
    | _ => return none

  /-- Full WHNF: whnfCore + delta + native reduction + nat prims, repeat until stuck. -/
  partial def whnfVal (v : Val m) (deltaSteps : Nat := 0) : TypecheckM σ m (Val m) := do
    let maxDelta := if (← read).eagerReduce then 500000 else 50000
    if deltaSteps > maxDelta then throw "whnfVal delta step limit exceeded"
    -- WHNF cache: check pointer-keyed cache (only at top-level entry)
    let vPtr := ptrAddrVal v
    if deltaSteps == 0 then
      heartbeat
      match (← get).whnfCache.get? vPtr with
      | some (inputRef, cached) =>
        if ptrEq v inputRef then
          return cached
      | none => pure ()
    let v' ← whnfCoreVal v
    let result ← do
      match ← tryReduceNatVal v' with
      | some v'' => whnfVal v'' (deltaSteps + 1)
      | none =>
        -- If v' is a nat prim whose args are genuinely stuck (no nat constructor/literal),
        -- delta-unfolding is wasteful: iota won't fire on the stuck recursor.
        -- Only block when NEITHER arg is a nat constructor; if either is (e.g., Nat.succ x),
        -- delta+iota will make progress. lazyDelta bypasses this (calls deltaStepVal directly).
        let skipDelta ← do
          let prims := (← read).prims
          if !isNatPrimHead prims v' then pure false
          else match v' with
            | .neutral _ spine =>
              if spine.isEmpty then pure false
              else
                let mut anyConstructor := false
                for i in [:min 2 spine.size] do
                  if h : i < spine.size then
                    let arg ← forceThunk spine[i]
                    let arg' ← whnfVal arg
                    if isNatConstructor prims arg' then
                      anyConstructor := true; break
                pure !anyConstructor
            | _ => pure false
        if skipDelta then pure v'
        else
          match ← tryEvalVal v' with
          | some v'' => whnfVal v'' (deltaSteps + 1)
          | none =>
            match ← deltaStepVal v' with
            | some v'' => whnfVal v'' (deltaSteps + 1)
            | none =>
              match ← reduceNativeVal v' with
              | some v'' =>
                -- Structural-only WHNF after native reduction to prevent re-entry.
                -- Matches Kernel1's approach (whnfCore, not whnfImpl).
                whnfCoreVal v''
              | none => pure v'
    -- Cache the final result (only at top-level entry)
    if deltaSteps == 0 then
      modify fun st => { st with
        whnfCache := st.whnfCache.insert vPtr (v, result) }
    pure result

  /-- Quick structural pre-check on Val: O(1) cases that don't need WHNF. -/
  partial def quickIsDefEqVal (t s : Val m) : Option Bool :=
    if ptrEq t s then some true
    else match t, s with
    | .sort u, .sort v => some (Ix.Kernel.Level.equalLevel u v)
    | .lit l, .lit l' => some (l == l')
    | .neutral (.const a us _) sp1, .neutral (.const b vs _) sp2 =>
      if a == b && equalUnivArrays us vs && sp1.isEmpty && sp2.isEmpty then some true
      else none
    | .ctor a us _ _ _ _ _ sp1, .ctor b vs _ _ _ _ _ sp2 =>
      if a == b && equalUnivArrays us vs && sp1.isEmpty && sp2.isEmpty then some true
      else none
    | _, _ => none

  /-- Check if two values are definitionally equal. -/
  partial def isDefEq (t s : Val m) : TypecheckM σ m Bool := do
    if let some result := quickIsDefEqVal t s then return result
    heartbeat
    -- 0. Pointer-based cache checks (keep alive to prevent GC address reuse)
    modify fun st => { st with keepAlive := st.keepAlive.push t |>.push s }
    let tPtr := ptrAddrVal t
    let sPtr := ptrAddrVal s
    let ptrKey := if tPtr ≤ sPtr then (tPtr, sPtr) else (sPtr, tPtr)
    -- 0a. EquivManager (union-find with transitivity)
    let stt ← get
    let (equiv, mgr') := EquivManager.isEquiv tPtr sPtr |>.run stt.eqvManager
    modify fun st => { st with eqvManager := mgr' }
    if equiv then return true
    -- 0b. Pointer failure cache (validate with ptrEq to guard against address reuse)
    match (← get).ptrFailureCache.get? ptrKey with
    | some (tRef, sRef) =>
      if (ptrEq t tRef && ptrEq s sRef) || (ptrEq t sRef && ptrEq s tRef) then
        return false
    | none => pure ()
    -- 1. Bool.true reflection
    let prims := (← read).prims
    if isBoolTrue prims s then
      let t' ← whnfVal t
      if isBoolTrue prims t' then return true
    if isBoolTrue prims t then
      let s' ← whnfVal s
      if isBoolTrue prims s' then return true
    -- 2. whnfCoreVal with cheapProj=true
    let tn ← whnfCoreVal t (cheapProj := true)
    let sn ← whnfCoreVal s (cheapProj := true)
    -- 3. Quick structural check after whnfCore
    if let some result := quickIsDefEqVal tn sn then return result
    -- 4. Proof irrelevance
    match ← isDefEqProofIrrel tn sn with
    | some result => return result
    | none => pure ()
    -- 5. Lazy delta reduction
    let (tn', sn', deltaResult) ← lazyDelta tn sn
    if let some result := deltaResult then return result
    -- 6. Cheap const check after delta (empty-spine only; non-empty goes to step 7)
    match tn', sn' with
    | .neutral (.const a us _) sp1, .neutral (.const b us' _) sp2 =>
      if a == b && equalUnivArrays us us' && sp1.isEmpty && sp2.isEmpty then return true
    | _, _ => pure ()
    -- 7. Full whnf (including delta) then structural comparison
    let tnn ← whnfVal tn'
    let snn ← whnfVal sn'
    let result ← isDefEqCore tnn snn
    -- 8. Cache result (union-find on success, ptr-based on failure)
    if result then
      let stt ← get
      let (_, mgr') := EquivManager.addEquiv tPtr sPtr |>.run stt.eqvManager
      modify fun st => { st with eqvManager := mgr' }
    else
      modify fun st => { st with ptrFailureCache := st.ptrFailureCache.insert ptrKey (t, s) }
    return result

  /-- Core structural comparison on values in WHNF. -/
  partial def isDefEqCore (t s : Val m) : TypecheckM σ m Bool := do
    if ptrEq t s then return true
    match t, s with
    -- Sort
    | .sort u, .sort v => pure (Ix.Kernel.Level.equalLevel u v)
    -- Literal
    | .lit l, .lit l' => pure (l == l')
    -- Neutral with fvar head
    | .neutral (.fvar l _) sp1, .neutral (.fvar l' _) sp2 =>
      if l != l' then return false
      isDefEqSpine sp1 sp2
    -- Neutral with const head
    | .neutral (.const a us _) sp1, .neutral (.const b vs _) sp2 =>
      if a != b || !equalUnivArrays us vs then return false
      isDefEqSpine sp1 sp2
    -- Constructor
    | .ctor a us _ _ _ _ _ sp1, .ctor b vs _ _ _ _ _ sp2 =>
      if a != b || !equalUnivArrays us vs then return false
      isDefEqSpine sp1 sp2
    -- Lambda: compare domains, then bodies under fresh binder
    | .lam name1 _ dom1 body1 env1, .lam _ _ dom2 body2 env2 => do
      if !(← isDefEq dom1 dom2) then return false
      let fv ← mkFreshFVar dom1
      let b1 ← eval body1 (env1.push fv)
      let b2 ← eval body2 (env2.push fv)
      withBinder dom1 name1 (isDefEq b1 b2)
    -- Pi: compare domains, then codomains under fresh binder
    | .pi name1 _ dom1 body1 env1, .pi _ _ dom2 body2 env2 => do
      if !(← isDefEq dom1 dom2) then return false
      let fv ← mkFreshFVar dom1
      let b1 ← eval body1 (env1.push fv)
      let b2 ← eval body2 (env2.push fv)
      withBinder dom1 name1 (isDefEq b1 b2)
    -- Eta: lambda vs non-lambda
    | .lam name1 _ dom body env, _ => do
      let fv ← mkFreshFVar dom
      let b1 ← eval body (env.push fv)
      let fvThunk ← mkThunkFromVal fv
      let s' ← applyValThunk s fvThunk
      withBinder dom name1 (isDefEq b1 s')
    | _, .lam name2 _ dom body env => do
      let fv ← mkFreshFVar dom
      let b2 ← eval body (env.push fv)
      let fvThunk ← mkThunkFromVal fv
      let t' ← applyValThunk t fvThunk
      withBinder dom name2 (isDefEq t' b2)
    -- Projection
    | .proj a i struct1 _ spine1, .proj b j struct2 _ spine2 =>
      if a == b && i == j then do
        let sv1 ← forceThunk struct1
        let sv2 ← forceThunk struct2
        if !(← isDefEq sv1 sv2) then return false
        isDefEqSpine spine1 spine2
      else pure false
    -- Nat literal ↔ constructor expansion
    | .lit (.natVal _), _ => do
      let t' ← natLitToCtorThunked t
      isDefEqCore t' s
    | _, .lit (.natVal _) => do
      let s' ← natLitToCtorThunked s
      isDefEqCore t s'
    -- String literal ↔ constructor expansion
    | .lit (.strVal str), _ => do
      let t' ← strLitToCtorThunked str
      isDefEq t' s
    | _, .lit (.strVal str) => do
      let s' ← strLitToCtorThunked str
      isDefEq t s'
    -- Fallback: try struct eta, then unit-like
    | _, _ => do
      if ← tryEtaStructVal t s then return true
      try isDefEqUnitLikeVal t s catch e =>
        if (← read).trace then dbg_trace s!"isDefEqCore: isDefEqUnitLikeVal threw: {e}"
        pure false

  /-- Compare two thunk spines element-wise (forcing each thunk). -/
  partial def isDefEqSpine (sp1 sp2 : Array Nat) : TypecheckM σ m Bool := do
    if sp1.size != sp2.size then return false
    for i in [:sp1.size] do
      if sp1[i]! == sp2[i]! then continue  -- same thunk, trivially equal
      let v1 ← forceThunk sp1[i]!
      let v2 ← forceThunk sp2[i]!
      if !(← isDefEq v1 v2) then return false
    return true

  /-- Lazy delta reduction: unfold definitions one at a time guided by hints.
      Single-step Krivine semantics — the caller controls unfolding. -/
  partial def lazyDelta (t s : Val m)
      : TypecheckM σ m (Val m × Val m × Option Bool) := do
    let mut tn := t
    let mut sn := s
    let kenv := (← read).kenv
    let mut steps := 0
    repeat
      heartbeat
      if steps > 10000 then throw "lazyDelta step limit exceeded"
      steps := steps + 1
      -- Pointer equality
      if ptrEq tn sn then return (tn, sn, some true)
      -- Quick structural
      match tn, sn with
      | .sort u, .sort v =>
        return (tn, sn, some (Ix.Kernel.Level.equalLevel u v))
      | .lit l, .lit l' =>
        return (tn, sn, some (l == l'))
      | _, _ => pure ()
      -- isDefEqOffset: short-circuit Nat.succ chain comparison
      match ← isDefEqOffset tn sn with
      | some result => return (tn, sn, some result)
      | none => pure ()
      -- Nat prim reduction
      if let some tn' ← tryReduceNatVal tn then
        return (tn', sn, some (← isDefEq tn' sn))
      if let some sn' ← tryReduceNatVal sn then
        return (tn, sn', some (← isDefEq tn sn'))
      -- Native reduction (reduceBool/reduceNat markers)
      if let some tn' ← reduceNativeVal tn then
        return (tn', sn, some (← isDefEq tn' sn))
      if let some sn' ← reduceNativeVal sn then
        return (tn, sn', some (← isDefEq tn sn'))
      -- Delta step: hint-guided, single-step
      let tDelta := getDeltaInfo tn kenv
      let sDelta := getDeltaInfo sn kenv
      match tDelta, sDelta with
      | none, none => return (tn, sn, none)  -- both stuck
      | some _, none =>
        match ← deltaStepVal tn with
        | some r => tn ← whnfCoreVal r (cheapProj := true); continue
        | none => return (tn, sn, none)
      | none, some _ =>
        match ← deltaStepVal sn with
        | some r => sn ← whnfCoreVal r (cheapProj := true); continue
        | none => return (tn, sn, none)
      | some (_, ht), some (_, hs) =>
        -- Same-head optimization with failure cache
        if sameHeadVal tn sn && ht.isRegular then
          if equalUnivArrays tn.headLevels! sn.headLevels! then
            let tPtr := ptrAddrVal tn
            let sPtr := ptrAddrVal sn
            let ptrKey := if tPtr ≤ sPtr then (tPtr, sPtr) else (sPtr, tPtr)
            let skipSpineCheck := match (← get).ptrFailureCache.get? ptrKey with
              | some (tRef, sRef) =>
                (ptrEq tn tRef && ptrEq sn sRef) || (ptrEq tn sRef && ptrEq sn tRef)
              | none => false
            if !skipSpineCheck then
              if ← isDefEqSpine tn.spine! sn.spine! then
                return (tn, sn, some true)
              else
                -- Record failure to prevent retrying after further unfolding
                modify fun st => { st with
                  ptrFailureCache := st.ptrFailureCache.insert ptrKey (tn, sn),
                  keepAlive := st.keepAlive.push tn |>.push sn }
        -- Hint-guided unfolding
        if ht.lt' hs then
          match ← deltaStepVal sn with
          | some r => sn ← whnfCoreVal r (cheapProj := true); continue
          | none =>
            match ← deltaStepVal tn with
            | some r => tn ← whnfCoreVal r (cheapProj := true); continue
            | none => return (tn, sn, none)
        else if hs.lt' ht then
          match ← deltaStepVal tn with
          | some r => tn ← whnfCoreVal r (cheapProj := true); continue
          | none =>
            match ← deltaStepVal sn with
            | some r => sn ← whnfCoreVal r (cheapProj := true); continue
            | none => return (tn, sn, none)
        else
          -- Same height: unfold both
          match ← deltaStepVal tn, ← deltaStepVal sn with
          | some rt, some rs =>
            tn ← whnfCoreVal rt (cheapProj := true)
            sn ← whnfCoreVal rs (cheapProj := true)
            continue
          | some rt, none => tn ← whnfCoreVal rt (cheapProj := true); continue
          | none, some rs => sn ← whnfCoreVal rs (cheapProj := true); continue
          | none, none => return (tn, sn, none)
    return (tn, sn, none)

  /-- Quote a value back to an expression at binding depth d.
      De Bruijn level l becomes bvar (d - 1 - l).
      `names` maps de Bruijn levels to binder names for readable pretty-printing. -/
  partial def quote (v : Val m) (d : Nat) (names : Array (KMetaField m Ix.Name) := #[])
      : TypecheckM σ m (KExpr m) := do
    -- Pad names to size d so names[level] works for any level < d.
    -- When no names provided, use context binderNames for the outer scope.
    let names ← do
      if names.isEmpty then
        let ctxNames := (← read).binderNames
        pure (if ctxNames.size < d then ctxNames ++ .replicate (d - ctxNames.size) default else ctxNames)
      else if names.size < d then pure (names ++ .replicate (d - names.size) default)
      else pure names
    match v with
    | .sort lvl => pure (.sort lvl)

    | .lam name bi dom body env => do
      let domE ← quote dom d names
      let freshVar := Val.mkFVar d dom
      let bodyV ← eval body (env.push freshVar)
      let bodyE ← quote bodyV (d + 1) (names.push name)
      pure (.lam domE bodyE name bi)

    | .pi name bi dom body env => do
      let domE ← quote dom d names
      let freshVar := Val.mkFVar d dom
      let bodyV ← eval body (env.push freshVar)
      let bodyE ← quote bodyV (d + 1) (names.push name)
      pure (.forallE domE bodyE name bi)

    | .neutral head spine => do
      let headE := quoteHead head d names
      let mut result := headE
      for thunkId in spine do
        let argV ← forceThunk thunkId
        let argE ← quote argV d names
        result := Ix.Kernel.Expr.mkApp result argE
      pure result

    | .ctor addr levels name _ _ _ _ spine => do
      let headE : KExpr m := .const addr levels name
      let mut result := headE
      for thunkId in spine do
        let argV ← forceThunk thunkId
        let argE ← quote argV d names
        result := Ix.Kernel.Expr.mkApp result argE
      pure result

    | .lit l => pure (.lit l)

    | .proj typeAddr idx structThunkId typeName spine => do
      let structV ← forceThunk structThunkId
      let structE ← quote structV d names
      let mut result : KExpr m := .proj typeAddr idx structE typeName
      for thunkId in spine do
        let argV ← forceThunk thunkId
        let argE ← quote argV d names
        result := Ix.Kernel.Expr.mkApp result argE
      pure result

  -- Type inference

  /-- Classify a type Val as proof/sort/unit/none. -/
  partial def infoFromType (typ : Val m) : TypecheckM σ m (KTypeInfo m) := do
    let typ' ← whnfVal typ
    match typ' with
    | .sort .zero => pure .proof
    | .sort lvl => pure (.sort lvl)
    | .neutral (.const addr _ _) _ =>
      match (← read).kenv.find? addr with
      | some (.inductInfo v) =>
        if v.ctors.size == 1 then
          match (← read).kenv.find? v.ctors[0]! with
          | some (.ctorInfo cv) =>
            if cv.numFields == 0 then pure .unit else pure .none
          | _ => pure .none
        else pure .none
      | _ => pure .none
    | _ => pure .none

  /-- Infer the type of an expression, returning typed expr and type as Val.
      Works on raw Expr — free bvars reference ctx.types (de Bruijn levels). -/
  partial def infer (term : KExpr m) : TypecheckM σ m (KTypedExpr m × Val m) := do
    heartbeat
    -- Inference cache: check if we've already inferred this term in the same context
    let ctx ← read
    match (← get).inferCache.get? term with
    | some (cachedTypes, te, typ) =>
        -- For consts/sorts/lits, context doesn't matter (always closed)
        let contextOk := match term with
          | .const .. | .sort .. | .lit .. => true
          | _ => arrayPtrEq cachedTypes ctx.types || arrayValPtrEq cachedTypes ctx.types
        if contextOk then
          return (te, typ)
    | none => pure ()
    let inferCore := do match term with
    | .bvar idx _ => do
      let ctx ← read
      let d := ctx.types.size
      if idx < d then
        let level := d - 1 - idx
        if h : level < ctx.types.size then
          let typ := ctx.types[level]
          let te : KTypedExpr m := ⟨← infoFromType typ, term⟩
          pure (te, typ)
        else
          throw s!"bvar {idx} out of range (depth={d})"
      else
        match ctx.mutTypes.get? (idx - d) with
        | some (addr, typeFn) =>
          if some addr == ctx.recAddr? then throw "Invalid recursion"
          let univs : Array (KLevel m) := #[]
          let typVal := typeFn univs
          let name ← lookupName addr
          let te : KTypedExpr m := ⟨← infoFromType typVal, .const addr univs name⟩
          pure (te, typVal)
        | none =>
          throw s!"bvar {idx} out of range (depth={d}, no mutual ref at {idx - d})"

    | .sort lvl => do
      let lvl' := Ix.Kernel.Level.succ lvl
      let typVal := Val.sort lvl'
      let te : KTypedExpr m := ⟨.sort lvl', term⟩
      pure (te, typVal)

    | .app .. => do
      let args := term.getAppArgs
      let fn := term.getAppFn
      let (_, fnType) ← infer fn
      let mut currentType := fnType
      let inferOnly := (← read).inferOnly
      for h : i in [:args.size] do
        let arg := args[i]
        let currentType' ← whnfVal currentType
        match currentType' with
        | .pi _ _ dom codBody codEnv => do
          if !inferOnly then
            let (_, argType) ← infer arg
            -- Check if arg is eagerReduce-wrapped (eagerReduce _ _)
            let prims := (← read).prims
            let isEager := prims.eagerReduce != default &&
              (match arg.getAppFn with
               | .const a _ _ => a == prims.eagerReduce
               | _ => false) &&
              arg.getAppNumArgs == 2
            let eq ← if isEager then
              withReader (fun ctx => { ctx with eagerReduce := true }) (isDefEq argType dom)
            else
              isDefEq argType dom
            if !eq then
              let d ← depth
              let ppArg ← quote argType d
              let ppDom ← quote dom d
              throw s!"app type mismatch\n  arg type: {ppArg.pp}\n  expected: {ppDom.pp}"
          let argVal ← evalInCtx arg
          currentType ← eval codBody (codEnv.push argVal)
        | _ =>
          let d ← depth
          let ppType ← quote currentType' d
          throw s!"Expected a pi type for application, got {ppType.pp}"
      let te : KTypedExpr m := ⟨← infoFromType currentType, term⟩
      pure (te, currentType)

    | .lam .. => do
      let inferOnly := (← read).inferOnly
      let mut cur := term
      let mut extTypes := (← read).types
      let mut extLetValues := (← read).letValues
      let mut extBinderNames := (← read).binderNames
      let mut domExprs : Array (KExpr m) := #[]  -- original domain Exprs for result type
      let mut lamBinderNames : Array (KMetaField m Ix.Name) := #[]
      let mut lamBinderInfos : Array (KMetaField m Lean.BinderInfo) := #[]
      repeat
        match cur with
        | .lam ty body name bi =>
          if !inferOnly then
            let _ ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
              (isSort ty)
          let domVal ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx ty)
          domExprs := domExprs.push ty
          lamBinderNames := lamBinderNames.push name
          lamBinderInfos := lamBinderInfos.push bi
          extTypes := extTypes.push domVal
          extLetValues := extLetValues.push none
          extBinderNames := extBinderNames.push name
          cur := body
        | _ => break
      let (_, bodyType) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
        (infer cur)
      -- Build the Pi type for the lambda: quote body type, wrap in forallEs, eval
      let d ← depth
      let numBinders := domExprs.size
      let mut resultTypeExpr ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
        (quote bodyType (d + numBinders))
      for i in [:numBinders] do
        let j := numBinders - 1 - i
        resultTypeExpr := .forallE domExprs[j]! resultTypeExpr lamBinderNames[j]! lamBinderInfos[j]!
      let resultTypeVal ← evalInCtx resultTypeExpr
      let te : KTypedExpr m := ⟨← infoFromType resultTypeVal, term⟩
      pure (te, resultTypeVal)

    | .forallE .. => do
      let mut cur := term
      let mut extTypes := (← read).types
      let mut extLetValues := (← read).letValues
      let mut extBinderNames := (← read).binderNames
      let mut sortLevels : Array (KLevel m) := #[]
      repeat
        match cur with
        | .forallE ty body name _ =>
          let (_, domLvl) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (isSort ty)
          sortLevels := sortLevels.push domLvl
          let domVal ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx ty)
          extTypes := extTypes.push domVal
          extLetValues := extLetValues.push none
          extBinderNames := extBinderNames.push name
          cur := body
        | _ => break
      let (_, imgLvl) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
        (isSort cur)
      let mut resultLvl := imgLvl
      for i in [:sortLevels.size] do
        let j := sortLevels.size - 1 - i
        resultLvl := Ix.Kernel.Level.reduceIMax sortLevels[j]! resultLvl
      let typVal := Val.sort resultLvl
      let te : KTypedExpr m := ⟨← infoFromType typVal, term⟩
      pure (te, typVal)

    | .letE .. => do
      let inferOnly := (← read).inferOnly
      let mut cur := term
      let mut extTypes := (← read).types
      let mut extLetValues := (← read).letValues
      let mut extBinderNames := (← read).binderNames
      repeat
        match cur with
        | .letE ty val body name =>
          if !inferOnly then
            let _ ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
              (isSort ty)
            let _ ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
              (checkExpr val ty)
          let tyVal ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx ty)
          let valVal ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx val)
          extTypes := extTypes.push tyVal
          extLetValues := extLetValues.push (some valVal)
          extBinderNames := extBinderNames.push name
          cur := body
        | _ => break
      let (bodyTe, bodyType) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
        (infer cur)
      -- In NbE, let values are already substituted by eval, so bodyType is correct as-is
      let te : KTypedExpr m := ⟨bodyTe.info, term⟩
      pure (te, bodyType)

    | .lit (.natVal _) => do
      let prims := (← read).prims
      let typVal := Val.mkConst prims.nat #[]
      let te : KTypedExpr m := ⟨.none, term⟩
      pure (te, typVal)

    | .lit (.strVal _) => do
      let prims := (← read).prims
      let typVal := Val.mkConst prims.string #[]
      let te : KTypedExpr m := ⟨.none, term⟩
      pure (te, typVal)

    | .const addr constUnivs _ => do
      ensureTypedConst addr
      let inferOnly := (← read).inferOnly
      if !inferOnly then
        let ci ← derefConst addr
        let curSafety := (← read).safety
        if ci.isUnsafe && curSafety != .unsafe then
          throw s!"invalid declaration, uses unsafe declaration"
        if let .defnInfo v := ci then
          if v.safety == .partial && curSafety == .safe then
            throw s!"safe declaration must not contain partial declaration"
        if constUnivs.size != ci.numLevels then
          throw s!"incorrect universe levels: expected {ci.numLevels}, got {constUnivs.size}"
      let tconst ← derefTypedConst addr
      let typExpr := tconst.type.body.instantiateLevelParams constUnivs
      let typVal ← evalInCtx typExpr
      let te : KTypedExpr m := ⟨← infoFromType typVal, term⟩
      pure (te, typVal)

    | .proj typeAddr idx struct _ => do
      let (structTe, structType) ← infer struct
      let (ctorType, ctorUnivs, numParams, params) ← getStructInfoVal structType
      let mut ct ← evalInCtx (ctorType.instantiateLevelParams ctorUnivs)
      -- Walk past params: apply each param to the codomain closure
      for paramVal in params do
        let ct' ← whnfVal ct
        match ct' with
        | .pi _ _ _ codBody codEnv =>
          ct ← eval codBody (codEnv.push paramVal)
        | _ => throw "Structure constructor has too few parameters"
      -- Walk past fields before idx
      let structVal ← evalInCtx struct
      let structThunkId ← mkThunkFromVal structVal
      for i in [:idx] do
        let ct' ← whnfVal ct
        match ct' with
        | .pi _ _ _ codBody codEnv =>
          let projVal := Val.proj typeAddr i structThunkId default #[]
          ct ← eval codBody (codEnv.push projVal)
        | _ => throw "Structure type does not have enough fields"
      -- Get the type at field idx
      let ct' ← whnfVal ct
      match ct' with
      | .pi _ _ dom _ _ =>
        let te : KTypedExpr m := ⟨← infoFromType dom, .proj typeAddr idx structTe.body default⟩
        pure (te, dom)
      | _ => throw "Structure type does not have enough fields"
    let result ← inferCore
    -- Insert into inference cache
    modify fun s => { s with inferCache := s.inferCache.insert term (ctx.types, result.1, result.2) }
    return result

  /-- Check that a term has the expected type. Bidirectional: pushes expected Pi
      type through lambda binders to avoid expensive infer+quote+isDefEq. -/
  partial def check (term : KExpr m) (expectedType : Val m)
      : TypecheckM σ m (KTypedExpr m) := do
    match term with
    | .lam ty body name bi =>
      let expectedWhnf ← whnfVal expectedType
      match expectedWhnf with
      | .pi piName _piBi piDom piBody piEnv =>
        -- BEq fast path: quote piDom and compare structurally against ty
        let d ← depth
        let piDomExpr ← quote piDom d
        if !(ty == piDomExpr) then
          -- Structural mismatch — fall back to full isDefEq on domains
          let lamDomV ← evalInCtx ty
          if !(← isDefEq lamDomV piDom) then
            let ppLamDom ← quote lamDomV d
            throw s!"Domain mismatch in check\n  lambda domain: {ppLamDom.pp}\n  expected domain: {piDomExpr.pp}"
        let fv ← mkFreshFVar piDom
        let expectedBody ← eval piBody (piEnv.push fv)
        withBinder piDom piName do
          let bodyTe ← check body expectedBody
          pure ⟨bodyTe.info, .lam ty bodyTe.body name bi⟩
      | _ =>
        -- Expected type is not a Pi after whnf — fall back to infer+compare
        let (te, inferredType) ← infer term
        if !(← isDefEq inferredType expectedType) then
          let d ← depth
          let ppInferred ← quote inferredType d
          let ppExpected ← quote expectedType d
          throw s!"Type mismatch on {term.tag}\n  inferred: {ppInferred.pp}\n  expected: {ppExpected.pp}"
        pure te
    | _ =>
      -- Non-lambda: infer + isDefEq as before
      let (te, inferredType) ← infer term
      if !(← isDefEq inferredType expectedType) then
        let d ← depth
        let ppInferred ← quote inferredType d
        let ppExpected ← quote expectedType d
        throw s!"Type mismatch on {term.tag}\n  inferred: {ppInferred.pp}\n  expected: {ppExpected.pp}"
      pure te

  /-- Also accept an Expr as expected type (eval it first). -/
  partial def checkExpr (term : KExpr m) (expectedTypeExpr : KExpr m)
      : TypecheckM σ m (KTypedExpr m) := do
    let expectedType ← evalInCtx expectedTypeExpr
    check term expectedType

  /-- Check if an expression is a Sort, returning the typed expr and the universe level. -/
  partial def isSort (expr : KExpr m) : TypecheckM σ m (KTypedExpr m × KLevel m) := do
    let (te, typ) ← infer expr
    let typ' ← whnfVal typ
    match typ' with
    | .sort u => pure (te, u)
    | _ =>
      let d ← depth
      let ppTyp ← quote typ' d
      throw s!"Expected a sort, got {ppTyp.pp}\n  expr: {expr.pp}"

  /-- Walk a Pi type, consuming spine args to compute the result type. -/
  partial def applySpineToType (ty : Val m) (spine : Array Nat)
      : TypecheckM σ m (Val m) := do
    let mut curType ← whnfVal ty
    for thunkId in spine do
      match curType with
      | .pi _ _ _dom body env =>
        let argV ← forceThunk thunkId
        curType ← eval body (env.push argV)
        curType ← whnfVal curType
      | _ => break
    pure curType

  /-- Infer the type of a Val directly, without quoting.
      Handles neutrals, sorts, lits, pi, proj. Falls back to quote+infer for lam. -/
  partial def inferTypeOfVal (v : Val m) : TypecheckM σ m (Val m) := do
    match v with
    | .sort lvl => pure (.sort (Ix.Kernel.Level.succ lvl))
    | .lit (.natVal _) => pure (Val.mkConst (← read).prims.nat #[])
    | .lit (.strVal _) => pure (Val.mkConst (← read).prims.string #[])
    | .neutral (.fvar _ type) spine => applySpineToType type spine
    | .neutral (.const addr levels _) spine =>
      ensureTypedConst addr
      let tc ← derefTypedConst addr
      let typExpr := tc.type.body.instantiateLevelParams levels
      let typVal ← evalInCtx typExpr
      applySpineToType typVal spine
    | .ctor addr levels _ _ _ _ _ spine =>
      ensureTypedConst addr
      let tc ← derefTypedConst addr
      let typExpr := tc.type.body.instantiateLevelParams levels
      let typVal ← evalInCtx typExpr
      applySpineToType typVal spine
    | .proj typeAddr idx structThunkId _ spine =>
      let structV ← forceThunk structThunkId
      let structType ← inferTypeOfVal structV
      let (ctorType, ctorUnivs, _numParams, params) ← getStructInfoVal structType
      let mut ct ← evalInCtx (ctorType.instantiateLevelParams ctorUnivs)
      for p in params do
        let ct' ← whnfVal ct
        match ct' with | .pi _ _ _ b e => ct ← eval b (e.push p) | _ => break
      let structThunkId' ← mkThunkFromVal structV
      for i in [:idx] do
        let ct' ← whnfVal ct
        match ct' with
        | .pi _ _ _ b e =>
          ct ← eval b (e.push (Val.proj typeAddr i structThunkId' default #[]))
        | _ => break
      let ct' ← whnfVal ct
      let fieldType ← match ct' with | .pi _ _ dom _ _ => pure dom | _ => pure ct'
      -- Apply spine to get result type (proj with spine is like a function application)
      applySpineToType fieldType spine
    | .pi name _ dom body env =>
      let domType ← inferTypeOfVal dom
      let domSort ← whnfVal domType
      let fv ← mkFreshFVar dom
      let codV ← eval body (env.push fv)
      let codType ← withBinder dom name (inferTypeOfVal codV)
      let codSort ← whnfVal codType
      match domSort, codSort with
      | .sort dl, .sort cl => pure (.sort (Ix.Kernel.Level.reduceIMax dl cl))
      | _, _ =>
        let d ← depth; let e ← quote v d
        let (_, ty) ← withInferOnly (infer e); pure ty
    | _ => -- .lam: fallback to quote+infer
      let d ← depth; let e ← quote v d
      let (_, ty) ← withInferOnly (infer e); pure ty

  /-- Check if a Val's type is Prop (Sort 0). Uses inferTypeOfVal to avoid quoting. -/
  partial def isPropVal (v : Val m) : TypecheckM σ m Bool := do
    let vType ← try inferTypeOfVal v catch e =>
      if (← read).trace then dbg_trace s!"isPropVal: inferTypeOfVal threw: {e}"
      return false
    let vType' ← whnfVal vType
    match vType' with
    | .sort .zero => pure true
    | _ => pure false

  -- isDefEq strategies

  /-- Look up ctor metadata from kenv by address. -/
  partial def mkCtorVal (addr : Address) (levels : Array (KLevel m)) (spine : Array Nat)
      (name : KMetaField m Ix.Name := default)
      : TypecheckM σ m (Val m) := do
    let kenv := (← read).kenv
    match kenv.find? addr with
    | some (.ctorInfo cv) =>
      pure (.ctor addr levels name cv.cidx cv.numParams cv.numFields cv.induct spine)
    | _ => pure (.neutral (.const addr levels name) spine)

  partial def natLitToCtorThunked (v : Val m) : TypecheckM σ m (Val m) := do
    let prims := (← read).prims
    match v with
    | .lit (.natVal 0) => mkCtorVal prims.natZero #[] #[]
    | .lit (.natVal (n+1)) =>
      let inner ← natLitToCtorThunked (.lit (.natVal n))
      let thunkId ← mkThunkFromVal inner
      mkCtorVal prims.natSucc #[] #[thunkId]
    | _ => pure v

  /-- Convert string literal to constructor form with thunks. -/
  partial def strLitToCtorThunked (s : String) : TypecheckM σ m (Val m) := do
    let prims := (← read).prims
    let charType := Val.mkConst prims.char #[]
    let charTypeThunk ← mkThunkFromVal charType
    let nilVal ← mkCtorVal prims.listNil #[.zero] #[charTypeThunk]
    let mut listVal := nilVal
    for c in s.toList.reverse do
      let charVal ← mkCtorVal prims.charMk #[] #[← mkThunkFromVal (.lit (.natVal c.toNat))]
      let ct ← mkThunkFromVal charType
      let ht ← mkThunkFromVal charVal
      let tt ← mkThunkFromVal listVal
      listVal ← mkCtorVal prims.listCons #[.zero] #[ct, ht, tt]
    let listThunk ← mkThunkFromVal listVal
    mkCtorVal prims.stringMk #[] #[listThunk]

  /-- Proof irrelevance: if both sides are proofs of Prop types, compare types. -/
  partial def isDefEqProofIrrel (t s : Val m) : TypecheckM σ m (Option Bool) := do
    let tType ← try inferTypeOfVal t catch e =>
      if (← read).trace then dbg_trace s!"isDefEqProofIrrel: inferTypeOfVal(t) threw: {e}"
      return none
    -- Check if tType : Prop (i.e., t is a proof, not just a type)
    if !(← isPropVal tType) then return none
    let sType ← try inferTypeOfVal s catch e =>
      if (← read).trace then dbg_trace s!"isDefEqProofIrrel: inferTypeOfVal(s) threw: {e}"
      return none
    some <$> isDefEq tType sType

  /-- Short-circuit Nat.succ chain / zero comparison. -/
  partial def isDefEqOffset (t s : Val m) : TypecheckM σ m (Option Bool) := do
    let prims := (← read).prims
    let isZero (v : Val m) : Bool := match v with
      | .lit (.natVal 0) => true
      | .neutral (.const addr _ _) spine => addr == prims.natZero && spine.isEmpty
      | .ctor addr _ _ _ _ _ _ spine => addr == prims.natZero && spine.isEmpty
      | _ => false
    -- Return thunk ID for Nat.succ, or lit predecessor; avoids forcing
    let succThunkId? (v : Val m) : Option Nat := match v with
      | .neutral (.const addr _ _) spine =>
        if addr == prims.natSucc && spine.size == 1 then some spine[0]! else none
      | .ctor addr _ _ _ _ _ _ spine =>
        if addr == prims.natSucc && spine.size == 1 then some spine[0]! else none
      | _ => none
    let succOf? (v : Val m) : TypecheckM σ m (Option (Val m)) := do
      match v with
      | .lit (.natVal (n+1)) => pure (some (.lit (.natVal n)))
      | .neutral (.const addr _ _) spine =>
        if addr == prims.natSucc && spine.size == 1 then
          pure (some (← forceThunk spine[0]!))
        else pure none
      | .ctor addr _ _ _ _ _ _ spine =>
        if addr == prims.natSucc && spine.size == 1 then
          pure (some (← forceThunk spine[0]!))
        else pure none
      | _ => pure none
    if isZero t && isZero s then return some true
    -- Thunk-ID short-circuit: if both succs share the same thunk, they're equal
    match succThunkId? t, succThunkId? s with
    | some tid1, some tid2 =>
      if tid1 == tid2 then return some true
      let t' ← forceThunk tid1
      let s' ← forceThunk tid2
      return some (← isDefEq t' s')
    | _, _ => pure ()
    match ← succOf? t, ← succOf? s with
    | some t', some s' => some <$> isDefEq t' s'
    | _, _ => return none

  /-- Structure eta core: if s is a ctor of a structure-like type, project t's fields. -/
  partial def tryEtaStructCoreVal (t s : Val m) : TypecheckM σ m Bool := do
    match s with
    | .ctor _ _ _ _ numParams numFields inductAddr spine =>
      let kenv := (← read).kenv
      unless spine.size == numParams + numFields do return false
      unless kenv.isStructureLike inductAddr do return false
      let tType ← try inferTypeOfVal t catch e =>
        if (← read).trace then dbg_trace s!"tryEtaStructCoreVal: inferTypeOfVal(t) threw: {e}"
        return false
      let sType ← try inferTypeOfVal s catch e =>
        if (← read).trace then dbg_trace s!"tryEtaStructCoreVal: inferTypeOfVal(s) threw: {e}"
        return false
      unless ← isDefEq tType sType do return false
      let tThunkId ← mkThunkFromVal t
      for _h : i in [:numFields] do
        let argIdx := numParams + i
        let projVal := Val.proj inductAddr i tThunkId default #[]
        let fieldVal ← forceThunk spine[argIdx]!
        unless ← isDefEq projVal fieldVal do return false
      return true
    | _ => return false

  /-- Structure eta: try both directions. -/
  partial def tryEtaStructVal (t s : Val m) : TypecheckM σ m Bool := do
    if ← tryEtaStructCoreVal t s then return true
    tryEtaStructCoreVal s t

  /-- Unit-like types: single ctor, 0 fields, 0 indices, non-recursive → compare types. -/
  partial def isDefEqUnitLikeVal (t s : Val m) : TypecheckM σ m Bool := do
    let kenv := (← read).kenv
    let tType ← try inferTypeOfVal t catch e =>
      if (← read).trace then dbg_trace s!"isDefEqUnitLikeVal: inferTypeOfVal(t) threw: {e}"
      return false
    let tType' ← whnfVal tType
    match tType' with
    | .neutral (.const addr _ _) _ =>
      match kenv.find? addr with
      | some (.inductInfo v) =>
        if v.isRec || v.numIndices != 0 || v.ctors.size != 1 then return false
        match kenv.find? v.ctors[0]! with
        | some (.ctorInfo cv) =>
          if cv.numFields != 0 then return false
          let sType ← try inferTypeOfVal s catch e =>
            if (← read).trace then dbg_trace s!"isDefEqUnitLikeVal: inferTypeOfVal(s) threw: {e}"
            return false
          isDefEq tType sType
        | _ => return false
      | _ => return false
    | _ => return false

  /-- Get structure info from a type Val.
      Returns (ctor type expr, universe levels, numParams, param vals). -/
  partial def getStructInfoVal (structType : Val m)
      : TypecheckM σ m (KExpr m × Array (KLevel m) × Nat × Array (Val m)) := do
    let structType' ← whnfVal structType
    match structType' with
    | .neutral (.const indAddr univs _) spine =>
      match (← read).kenv.find? indAddr with
      | some (.inductInfo v) =>
        if v.ctors.size != 1 then
          throw s!"Expected a structure type (single constructor)"
        if spine.size != v.numParams then
          throw s!"Wrong number of params for structure: got {spine.size}, expected {v.numParams}"
        ensureTypedConst indAddr
        let ctorAddr := v.ctors[0]!
        ensureTypedConst ctorAddr
        match (← get).typedConsts.get? ctorAddr with
        | some (.constructor type _ _) =>
          let mut params := #[]
          for thunkId in spine do
            params := params.push (← forceThunk thunkId)
          return (type.body, univs, v.numParams, params)
        | _ => throw s!"Constructor not in typedConsts"
      | some ci => throw s!"Expected a structure type, got {ci.kindName}"
      | none => throw s!"Type not found in environment"
    | _ =>
      let d ← depth
      let ppType ← quote structType' d
      throw s!"Expected a structure type, got {ppType.pp}"

  -- Declaration checking

  /-- Build a KernelOps2 adapter bridging Val-based operations to Expr-based interface. -/
  partial def mkOps : KernelOps2 σ m := {
    isDefEq := fun a b => do
      let va ← evalInCtx a
      let vb ← evalInCtx b
      isDefEq va vb
    whnf := fun e => do
      let v ← evalInCtx e
      let v' ← whnfVal v
      let d ← depth
      quote v' d
    infer := fun e => do
      let (te, typVal) ← infer e
      let d ← depth
      let typExpr ← quote typVal d
      pure (te, typExpr)
    isProp := fun e => do
      let (_, typVal) ← infer e
      let typVal' ← whnfVal typVal
      match typVal' with
      | .sort .zero => pure true
      | _ => pure false
    isSort := fun e => do
      isSort e
  }

  /-- Validate a primitive definition/inductive using the KernelOps2 adapter. -/
  partial def validatePrimitive (addr : Address) : TypecheckM σ m Unit := do
    let ops := mkOps
    let prims := (← read).prims
    let kenv := (← read).kenv
    let _ ← checkPrimitive ops prims kenv addr

  /-- Validate quotient constant type signatures. -/
  partial def validateQuotient : TypecheckM σ m Unit := do
    let ops := mkOps
    let prims := (← read).prims
    checkEqType ops prims
    checkQuotTypes ops prims

  /-- Walk a Pi chain to extract the return sort level. -/
  partial def getReturnSort (expr : KExpr m) (numBinders : Nat) : TypecheckM σ m (KLevel m) :=
    match numBinders, expr with
    | 0, .sort u => pure u
    | 0, _ => do
      let (_, typ) ← infer expr
      let typ' ← whnfVal typ
      match typ' with
      | .sort u => pure u
      | _ => throw "inductive return type is not a sort"
    | n+1, .forallE dom body name _ => do
      let _ ← isSort dom
      let domV ← evalInCtx dom
      withBinder domV name (getReturnSort body n)
    | _, _ => throw "inductive type has fewer binders than expected"

  /-- Check nested inductive constructor fields for positivity. -/
  partial def checkNestedCtorFields (ctorType : KExpr m) (numParams : Nat)
      (paramArgs : Array (KExpr m)) (indAddrs : Array Address) : TypecheckM σ m Bool := do
    let mut ty := ctorType
    for _ in [:numParams] do
      match ty with
      | .forallE _ body _ _ => ty := body
      | _ => return true
    ty := ty.instantiate paramArgs.reverse
    loop ty
  where
    loop (ty : KExpr m) : TypecheckM σ m Bool := do
      let tyE ← evalInCtx ty
      let ty' ← whnfVal tyE
      let d ← depth
      let tyExpr ← quote ty' d
      match tyExpr with
      | .forallE dom body _ _ =>
        if !(← checkPositivity dom indAddrs) then return false
        loop body
      | _ => return true

  /-- Check strict positivity of a field type w.r.t. inductive addresses. -/
  partial def checkPositivity (ty : KExpr m) (indAddrs : Array Address) : TypecheckM σ m Bool := do
    let tyV ← evalInCtx ty
    let ty' ← whnfVal tyV
    let d ← depth
    let tyExpr ← quote ty' d
    if !indAddrs.any (Ix.Kernel.exprMentionsConst tyExpr ·) then return true
    match tyExpr with
    | .forallE dom body _ _ =>
      if indAddrs.any (Ix.Kernel.exprMentionsConst dom ·) then return false
      checkPositivity body indAddrs
    | e =>
      let fn := e.getAppFn
      match fn with
      | .const addr _ _ =>
        if indAddrs.any (· == addr) then return true
        match (← read).kenv.find? addr with
        | some (.inductInfo fv) =>
          if fv.isUnsafe then return false
          let args := e.getAppArgs
          for i in [fv.numParams:args.size] do
            if indAddrs.any (Ix.Kernel.exprMentionsConst args[i]! ·) then return false
          let paramArgs := args[:fv.numParams].toArray
          let augmented := indAddrs ++ fv.all
          for ctorAddr in fv.ctors do
            match (← read).kenv.find? ctorAddr with
            | some (.ctorInfo cv) =>
              if !(← checkNestedCtorFields cv.type fv.numParams paramArgs augmented) then
                return false
            | _ => return false
          return true
        | _ => return false
      | _ => return false

  /-- Walk a Pi chain, skip numParams binders, then check positivity of each field. -/
  partial def checkCtorFields (ctorType : KExpr m) (numParams : Nat) (indAddrs : Array Address)
      : TypecheckM σ m (Option String) :=
    go ctorType numParams
  where
    go (ty : KExpr m) (remainingParams : Nat) : TypecheckM σ m (Option String) := do
      let tyV ← evalInCtx ty
      let ty' ← whnfVal tyV
      let d ← depth
      let tyExpr ← quote ty' d
      match tyExpr with
      | .forallE dom body name _ =>
        let domV ← evalInCtx dom
        if remainingParams > 0 then
          withBinder domV name (go body (remainingParams - 1))
        else
          if !(← checkPositivity dom indAddrs) then
            return some "inductive occurs in negative position (strict positivity violation)"
          withBinder domV name (go body 0)
      | _ => return none

  /-- Check that constructor field types have sorts <= the inductive's result sort. -/
  partial def checkFieldUniverses (ctorType : KExpr m) (numParams : Nat)
      (ctorAddr : Address) (indLvl : KLevel m) : TypecheckM σ m Unit :=
    go ctorType numParams
  where
    go (ty : KExpr m) (remainingParams : Nat) : TypecheckM σ m Unit := do
      let tyV ← evalInCtx ty
      let ty' ← whnfVal tyV
      let d ← depth
      let tyExpr ← quote ty' d
      match tyExpr with
      | .forallE dom body piName _ =>
        if remainingParams > 0 then do
          let _ ← isSort dom
          let domV ← evalInCtx dom
          withBinder domV piName (go body (remainingParams - 1))
        else do
          let (_, fieldSortLvl) ← isSort dom
          let fieldReduced := Ix.Kernel.Level.reduce fieldSortLvl
          let indReduced := Ix.Kernel.Level.reduce indLvl
          if !Ix.Kernel.Level.leq fieldReduced indReduced 0 && !Ix.Kernel.Level.isZero indReduced then
            throw s!"Constructor {ctorAddr} field type lives in a universe larger than the inductive's universe"
          let domV ← evalInCtx dom
          withBinder domV piName (go body 0)
      | _ => pure ()

  /-- Check if a single-ctor Prop inductive allows large elimination. -/
  partial def checkLargeElimSingleCtor (ctorType : KExpr m) (numParams numFields : Nat)
      : TypecheckM σ m Bool :=
    go ctorType numParams numFields #[]
  where
    go (ty : KExpr m) (remainingParams : Nat) (remainingFields : Nat)
       (nonPropBvars : Array Nat) : TypecheckM σ m Bool := do
      let tyV ← evalInCtx ty
      let ty' ← whnfVal tyV
      let d ← depth
      let tyExpr ← quote ty' d
      match tyExpr with
      | .forallE dom body piName _ =>
        if remainingParams > 0 then
          let domV ← evalInCtx dom
          withBinder domV piName (go body (remainingParams - 1) remainingFields nonPropBvars)
        else if remainingFields > 0 then
          let (_, fieldSortLvl) ← isSort dom
          let nonPropBvars := if !Ix.Kernel.Level.isZero fieldSortLvl then
            nonPropBvars.push (remainingFields - 1)
          else nonPropBvars
          let domV ← evalInCtx dom
          withBinder domV piName (go body 0 (remainingFields - 1) nonPropBvars)
        else pure true
      | _ =>
        if nonPropBvars.isEmpty then return true
        let args := tyExpr.getAppArgs
        for bvarIdx in nonPropBvars do
          let mut found := false
          for i in [numParams:args.size] do
            match args[i]! with
            | .bvar idx _ => if idx == bvarIdx then found := true
            | _ => pure ()
          if !found then return false
        return true

  /-- Validate that the recursor's elimination level is appropriate for the inductive. -/
  partial def checkElimLevel (recType : KExpr m) (rec : Ix.Kernel.RecursorVal m) (indAddr : Address)
      : TypecheckM σ m Unit := do
    let kenv := (← read).kenv
    match kenv.find? indAddr with
    | some (.inductInfo iv) =>
      let some indLvl := Ix.Kernel.getIndResultLevel iv.type | return ()
      if Ix.Kernel.levelIsNonZero indLvl then return ()
      let some motiveSort := Ix.Kernel.getMotiveSort recType rec.numParams | return ()
      if Ix.Kernel.Level.isZero motiveSort then return ()
      if iv.all.size != 1 then
        throw "recursor claims large elimination but mutual Prop inductive only allows Prop elimination"
      if iv.ctors.isEmpty then return ()
      if iv.ctors.size != 1 then
        throw "recursor claims large elimination but Prop inductive with multiple constructors only allows Prop elimination"
      let ctorAddr := iv.ctors[0]!
      match kenv.find? ctorAddr with
      | some (.ctorInfo cv) =>
        let allowed ← checkLargeElimSingleCtor cv.type iv.numParams cv.numFields
        if !allowed then
          throw "recursor claims large elimination but inductive has non-Prop fields not appearing in indices"
      | _ => return ()
    | _ => return ()

  /-- Validate K-flag: requires non-mutual, Prop, single ctor, zero fields. -/
  partial def validateKFlag (indAddr : Address) : TypecheckM σ m Unit := do
    match (← read).kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if iv.all.size != 1 then throw "recursor claims K but inductive is mutual"
      match Ix.Kernel.getIndResultLevel iv.type with
      | some lvl =>
        if Ix.Kernel.levelIsNonZero lvl then throw "recursor claims K but inductive is not in Prop"
      | none => throw "recursor claims K but cannot determine inductive's result sort"
      if iv.ctors.size != 1 then
        throw s!"recursor claims K but inductive has {iv.ctors.size} constructors (need 1)"
      match (← read).kenv.find? iv.ctors[0]! with
      | some (.ctorInfo cv) =>
        if cv.numFields != 0 then
          throw s!"recursor claims K but constructor has {cv.numFields} fields (need 0)"
      | _ => throw "recursor claims K but constructor not found"
    | _ => throw s!"recursor claims K but {indAddr} is not an inductive"

  /-- Validate recursor rules: rule count, ctor membership, field counts. -/
  partial def validateRecursorRules (rec : Ix.Kernel.RecursorVal m) (indAddr : Address) : TypecheckM σ m Unit := do
    match (← read).kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if rec.rules.size != iv.ctors.size then
        throw s!"recursor has {rec.rules.size} rules but inductive has {iv.ctors.size} constructors"
      for h : i in [:rec.rules.size] do
        let rule := rec.rules[i]
        match (← read).kenv.find? iv.ctors[i]! with
        | some (.ctorInfo cv) =>
          if rule.nfields != cv.numFields then
            throw s!"recursor rule for {iv.ctors[i]!} has nfields={rule.nfields} but constructor has {cv.numFields} fields"
        | _ => throw s!"constructor {iv.ctors[i]!} not found"
    | _ => pure ()

  /-- Check that a recursor rule RHS has the expected type.
      Uses bidirectional check to push expected type through lambda binders. -/
  partial def checkRecursorRuleType (recType : KExpr m) (rec : Ix.Kernel.RecursorVal m)
      (ctorAddr : Address) (nf : Nat) (ruleRhs : KExpr m)
      : TypecheckM σ m (KTypedExpr m) := do
    let np := rec.numParams
    let nm := rec.numMotives
    let nk := rec.numMinors
    let shift := nm + nk
    let ctorCi ← derefConst ctorAddr
    let ctorType := ctorCi.type
    let mut recTy := recType
    let mut recDoms : Array (KExpr m) := #[]
    for _ in [:np + nm + nk] do
      match recTy with
      | .forallE dom body _ _ =>
        recDoms := recDoms.push dom
        recTy := body
      | _ => throw "recursor type has too few Pi binders for params+motives+minors"
    let ni := rec.numIndices
    let motivePos : Nat := Id.run do
      let mut ty := recTy
      for _ in [:ni + 1] do
        match ty with
        | .forallE _ body _ _ => ty := body
        | _ => return 0
      match ty.getAppFn with
      | .bvar idx _ => return (ni + nk + nm - idx)
      | _ => return 0
    let cnp := match ctorCi with | .ctorInfo cv => cv.numParams | _ => np
    let majorPremiseDom : Option (KExpr m) := Id.run do
      let mut ty := recTy
      for _ in [:ni] do
        match ty with
        | .forallE _ body _ _ => ty := body
        | _ => return none
      match ty with
      | .forallE dom _ _ _ => return some dom
      | _ => return none
    let recLevelCount := rec.numLevels
    let ctorLevelCount := ctorCi.cv.numLevels
    let levelSubst : Array (KLevel m) :=
      if cnp > np then
        match majorPremiseDom with
        | some dom => match dom.getAppFn with
          | .const _ lvls _ => lvls
          | _ => #[]
        | none => #[]
      else
        let levelOffset := recLevelCount - ctorLevelCount
        Array.ofFn (n := ctorLevelCount) fun i =>
          .param (levelOffset + i.val) (default : Ix.Kernel.MetaField m Ix.Name)
    let ctorLevels := levelSubst
    let nestedParams : Array (KExpr m) :=
      if cnp > np then
        match majorPremiseDom with
        | some dom =>
          let args := dom.getAppArgs
          Array.ofFn (n := cnp - np) fun i =>
            if np + i.val < args.size then
              Ix.Kernel.shiftCtorToRule args[np + i.val]! 0 nf #[]
            else default
        | none => #[]
      else #[]
    let mut cty := ctorType
    for _ in [:cnp] do
      match cty with
      | .forallE _ body _ _ => cty := body
      | _ => throw "constructor type has too few Pi binders for params"
    let mut fieldDoms : Array (KExpr m) := #[]
    let mut ctorRetType := cty
    for _ in [:nf] do
      match ctorRetType with
      | .forallE dom body _ _ =>
        fieldDoms := fieldDoms.push dom
        ctorRetType := body
      | _ => throw "constructor type has too few Pi binders for fields"
    let ctorRet := if cnp > np then
      Ix.Kernel.substNestedParams ctorRetType nf (cnp - np) nestedParams
    else ctorRetType
    let fieldDomsAdj := if cnp > np then
      Array.ofFn (n := fieldDoms.size) fun i =>
        Ix.Kernel.substNestedParams fieldDoms[i]! i.val (cnp - np) nestedParams
    else fieldDoms
    let ctorRetShifted := Ix.Kernel.shiftCtorToRule ctorRet nf shift levelSubst
    let motiveIdx := nf + nk + nm - 1 - motivePos
    let mut ret := Ix.Kernel.Expr.mkBVar motiveIdx
    let ctorRetArgs := ctorRetShifted.getAppArgs
    for i in [cnp:ctorRetArgs.size] do
      ret := Ix.Kernel.Expr.mkApp ret ctorRetArgs[i]!
    let mut ctorApp : KExpr m := Ix.Kernel.Expr.mkConst ctorAddr ctorLevels
    for i in [:np] do
      ctorApp := Ix.Kernel.Expr.mkApp ctorApp (Ix.Kernel.Expr.mkBVar (nf + shift + np - 1 - i))
    for v in nestedParams do
      ctorApp := Ix.Kernel.Expr.mkApp ctorApp v
    for k in [:nf] do
      ctorApp := Ix.Kernel.Expr.mkApp ctorApp (Ix.Kernel.Expr.mkBVar (nf - 1 - k))
    ret := Ix.Kernel.Expr.mkApp ret ctorApp
    -- Build suffix: field binders + return type (without prefix wrapping)
    let mut suffixType := ret
    for i in [:nf] do
      let j := nf - 1 - i
      let dom := Ix.Kernel.shiftCtorToRule fieldDomsAdj[j]! j shift levelSubst
      suffixType := .forallE dom suffixType default default
    -- Build full expected type: prefix (params+motives+minors) + suffix
    let mut fullType := suffixType
    for i in [:np + nm + nk] do
      let j := np + nm + nk - 1 - i
      fullType := .forallE recDoms[j]! fullType default default
    -- Walk ruleRhs (lambdas) and fullType (forallEs) in parallel as KExprs,
    -- comparing domain KExprs directly with BEq (no eval/quote round-trip).
    let mut rhs := ruleRhs
    let mut expected := fullType
    let mut extTypes := (← read).types
    let mut extLetValues := (← read).letValues
    let mut extBinderNames := (← read).binderNames
    let mut lamDoms : Array (KExpr m) := #[]
    let mut lamNames : Array (KMetaField m Ix.Name) := #[]
    let mut lamBis : Array (KMetaField m Lean.BinderInfo) := #[]
    repeat
      match rhs, expected with
      | .lam ty body name bi, .forallE dom expBody _ _ =>
        -- BEq fast path: compare domain KExprs directly (no eval needed)
        if !(ty == dom) then
          let tyV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx ty)
          let domV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (evalInCtx dom)
          if !(← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
            (withInferOnly (isDefEq tyV domV))) then
            throw s!"recursor rule domain mismatch for {ctorAddr}"
        let domV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
          (evalInCtx dom)
        lamDoms := lamDoms.push ty
        lamNames := lamNames.push name
        lamBis := lamBis.push bi
        extTypes := extTypes.push domV
        extLetValues := extLetValues.push none
        extBinderNames := extBinderNames.push name
        rhs := body
        expected := expBody
      | _, _ => break
    -- Check body: infer and compare against expected return type
    let (bodyTe, bodyType) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
      (withInferOnly (infer rhs))
    let expectedRetV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
      (evalInCtx expected)
    if !(← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
      (withInferOnly (isDefEq bodyType expectedRetV))) then
      throw s!"recursor rule body type mismatch for {ctorAddr}"
    -- Rebuild KTypedExpr: wrap body in lambda binders
    let mut resultBody := bodyTe.body
    for i in [:lamDoms.size] do
      let j := lamDoms.size - 1 - i
      resultBody := .lam lamDoms[j]! resultBody lamNames[j]! lamBis[j]!
    pure ⟨bodyTe.info, resultBody⟩

  /-- Typecheck a mutual inductive block. -/
  partial def checkIndBlock (addr : Address) : TypecheckM σ m Unit := do
    let ci ← derefConst addr
    let indInfo ← match ci with
      | .inductInfo _ => pure ci
      | .ctorInfo v =>
        match (← read).kenv.find? v.induct with
        | some ind@(.inductInfo ..) => pure ind
        | _ => throw "Constructor's inductive not found"
      | _ => throw "Expected an inductive"
    let .inductInfo iv := indInfo | throw "unreachable"
    if (← get).typedConsts.get? addr |>.isSome then return ()
    let (type, _) ← isSort iv.type
    validatePrimitive addr
    let isStruct := !iv.isRec && iv.numIndices == 0 && iv.ctors.size == 1 &&
      match (← read).kenv.find? iv.ctors[0]! with
      | some (.ctorInfo cv) => cv.numFields > 0
      | _ => false
    modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr (Ix.Kernel.TypedConst.inductive type isStruct) }
    let indAddrs := iv.all
    let indResultLevel := Ix.Kernel.getIndResultLevel iv.type
    for (ctorAddr, _cidx) in iv.ctors.toList.zipIdx do
      match (← read).kenv.find? ctorAddr with
      | some (.ctorInfo cv) => do
        let (ctorType, _) ← isSort cv.type
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert ctorAddr (Ix.Kernel.TypedConst.constructor ctorType cv.cidx cv.numFields) }
        if cv.numParams != iv.numParams then
          throw s!"Constructor {ctorAddr} has {cv.numParams} params but inductive has {iv.numParams}"
        if !iv.isUnsafe then do
          let mut indTy := iv.type
          let mut ctorTy := cv.type
          let mut extTypes := (← read).types
          let mut extLetValues := (← read).letValues
          let mut extBinderNames := (← read).binderNames
          for i in [:iv.numParams] do
            match indTy, ctorTy with
            | .forallE indDom indBody indName _, .forallE ctorDom ctorBody _ _ =>
              let indDomV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
                (evalInCtx indDom)
              let ctorDomV ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
                (evalInCtx ctorDom)
              if !(← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, binderNames := extBinderNames })
                (isDefEq indDomV ctorDomV)) then
                throw s!"Constructor {ctorAddr} parameter {i} domain doesn't match inductive parameter domain"
              extTypes := extTypes.push indDomV
              extLetValues := extLetValues.push none
              extBinderNames := extBinderNames.push indName
              indTy := indBody
              ctorTy := ctorBody
            | _, _ =>
              throw s!"Constructor {ctorAddr} has fewer Pi binders than expected parameters"
        if !iv.isUnsafe then
          match ← checkCtorFields cv.type cv.numParams indAddrs with
          | some msg => throw s!"Constructor {ctorAddr}: {msg}"
          | none => pure ()
        if !iv.isUnsafe then
          if let some indLvl := indResultLevel then
            checkFieldUniverses cv.type cv.numParams ctorAddr indLvl
        if !iv.isUnsafe then
          let retType := Ix.Kernel.getCtorReturnType cv.type cv.numParams cv.numFields
          let retHead := retType.getAppFn
          match retHead with
          | .const retAddr _ _ =>
            if !indAddrs.any (· == retAddr) then
              throw s!"Constructor {ctorAddr} return type head is not the inductive being defined"
          | _ =>
            throw s!"Constructor {ctorAddr} return type is not an inductive application"
          let args := retType.getAppArgs
          for i in [:iv.numParams] do
            if i < args.size then
              let expectedBvar := cv.numFields + iv.numParams - 1 - i
              match args[i]! with
              | .bvar idx _ =>
                if idx != expectedBvar then
                  throw s!"Constructor {ctorAddr} return type has wrong parameter at position {i}"
              | _ =>
                throw s!"Constructor {ctorAddr} return type parameter {i} is not a bound variable"
          for i in [iv.numParams:args.size] do
            for indAddr in indAddrs do
              if Ix.Kernel.exprMentionsConst args[i]! indAddr then
                throw s!"Constructor {ctorAddr} index argument mentions the inductive (unsound)"
      | _ => throw s!"Constructor {ctorAddr} not found"

  /-- Typecheck a single constant declaration. -/
  partial def checkConst (addr : Address) : TypecheckM σ m Unit := withResetCtx do
    let ci? := (← read).kenv.find? addr
    let declSafety := match ci? with | some ci => ci.safety | none => .safe
    withSafety declSafety do
    -- Reset all ephemeral caches and thunk table between constants
    (← read).thunkTable.set #[]
    modify fun stt => { stt with
      ptrFailureCache := default,
      eqvManager := {},
      keepAlive := #[],
      whnfCache := default,
      whnfCoreCache := default,
      inferCache := default,
      heartbeats := 0
    }
    if (← get).typedConsts.get? addr |>.isSome then return ()
    let ci ← derefConst addr
    let _univs := ci.cv.mkUnivParams
    let newConst ← match ci with
      | .axiomInfo _ =>
        let (type, _) ← isSort ci.type
        pure (Ix.Kernel.TypedConst.axiom type)
      | .opaqueInfo _ =>
        let (type, _) ← isSort ci.type
        let typeV ← evalInCtx type.body
        let value ← withRecAddr addr (check ci.value?.get! typeV)
        pure (Ix.Kernel.TypedConst.opaque type value)
      | .thmInfo _ =>
        let (type, lvl) ← withInferOnly (isSort ci.type)
        if !Ix.Kernel.Level.isZero lvl then
          throw "theorem type must be a proposition (Sort 0)"
        let (_, valType) ← withRecAddr addr (withInferOnly (infer ci.value?.get!))
        let typeV ← evalInCtx type.body
        if !(← withInferOnly (isDefEq valType typeV)) then
          throw "theorem value type doesn't match declared type"
        let value : KTypedExpr m := ⟨.proof, ci.value?.get!⟩
        pure (Ix.Kernel.TypedConst.theorem type value)
      | .defnInfo v =>
        let (type, _) ← isSort ci.type
        let part := v.safety == .partial
        let typeV ← evalInCtx type.body
        let hb0 ← pure (← get).heartbeats
        let value ←
          if part then
            let typExpr := type.body
            let mutTypes : Std.TreeMap Nat (Address × (Array (KLevel m) → Val m)) compare :=
              (Std.TreeMap.empty).insert 0 (addr, fun _ => Val.neutral (.const addr #[] default) #[])
            withMutTypes mutTypes (withRecAddr addr (check v.value typeV))
          else withRecAddr addr (check v.value typeV)
        let hb1 ← pure (← get).heartbeats
        if (← read).trace then
          dbg_trace s!"  [defn] check value: {hb1 - hb0} heartbeats"
        validatePrimitive addr
        pure (Ix.Kernel.TypedConst.definition type value part)
      | .quotInfo v =>
        let (type, _) ← isSort ci.type
        if (← read).quotInit then
          validateQuotient
        pure (Ix.Kernel.TypedConst.quotient type v.kind)
      | .inductInfo _ =>
        checkIndBlock addr
        return ()
      | .ctorInfo v =>
        checkIndBlock v.induct
        return ()
      | .recInfo v => do
        let indAddr := getMajorInduct ci.type v.numParams v.numMotives v.numMinors v.numIndices
          |>.getD default
        ensureTypedConst indAddr
        let (type, _) ← isSort ci.type
        if v.k then
          validateKFlag indAddr
        validateRecursorRules v indAddr
        checkElimLevel ci.type v indAddr
        let hb0 ← pure (← get).heartbeats
        let mut typedRules : Array (Nat × KTypedExpr m) := #[]
        match (← read).kenv.find? indAddr with
        | some (.inductInfo iv) =>
          for h : i in [:v.rules.size] do
            let rule := v.rules[i]
            if i < iv.ctors.size then
              let hbr0 ← pure (← get).heartbeats
              let rhs ← checkRecursorRuleType ci.type v iv.ctors[i]! rule.nfields rule.rhs
              typedRules := typedRules.push (rule.nfields, rhs)
              let hbr1 ← pure (← get).heartbeats
              if (← read).trace then
                dbg_trace s!"  [rec] checkRecursorRuleType rule {i}: {hbr1 - hbr0} heartbeats"
        | _ => pure ()
        let hb1 ← pure (← get).heartbeats
        if (← read).trace then
          dbg_trace s!"  [rec] checkRecursorRuleType total: {hb1 - hb0} heartbeats ({v.rules.size} rules)"
        pure (Ix.Kernel.TypedConst.recursor type v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules)
    modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr newConst }

end

/-! ## Convenience wrappers -/

/-- Evaluate an expression to WHNF and quote back. -/
def whnf (e : KExpr m) : TypecheckM σ m (KExpr m) := do
  let v ← evalInCtx e
  let v' ← whnfVal v
  let d ← depth
  quote v' d

/-- Evaluate a closed expression to a value (no local env). -/
def evalClosed (e : KExpr m) : TypecheckM σ m (Val m) :=
  evalInCtx e

/-- Force to WHNF and quote a value. -/
def forceQuote (v : Val m) : TypecheckM σ m (KExpr m) := do
  let v' ← whnfVal v
  let d ← depth
  quote v' d

/-- Infer the type of a closed expression (no local env). -/
def inferClosed (e : KExpr m) : TypecheckM σ m (KTypedExpr m × Val m) :=
  infer e

/-- Infer type and quote it back to Expr. -/
def inferQuote (e : KExpr m) : TypecheckM σ m (KTypedExpr m × KExpr m) := do
  let (te, typVal) ← infer e
  let d ← depth
  let typExpr ← quote typVal d
  pure (te, typExpr)

/-! ## Top-level typechecking entry points -/

/-- Typecheck a single constant by address. -/
def typecheckConst (kenv : KEnv m) (prims : KPrimitives) (addr : Address)
    (quotInit : Bool := true) (trace : Bool := false) : Except String Unit :=
  TypecheckM.runPure
    (fun _σ tt => { types := #[], kenv, prims, safety := .safe, quotInit, trace, thunkTable := tt })
    {}
    (fun _σ => checkConst addr)
  |>.map (·.1)

/-- Typecheck all constants in an environment. Returns first error. -/
def typecheckAll (kenv : KEnv m) (prims : KPrimitives)
    (quotInit : Bool := true) : Except String Unit := do
  for (addr, ci) in kenv do
    match typecheckConst kenv prims addr quotInit with
    | .ok () => pure ()
    | .error e =>
      throw s!"constant {ci.cv.name} ({ci.kindName}, {addr}): {e}"

/-- Typecheck all constants with IO progress reporting. -/
def typecheckAllIO (kenv : KEnv m) (prims : KPrimitives)
    (quotInit : Bool := true) : IO (Except String Unit) := do
  let mut items : Array (Address × Ix.Kernel.ConstantInfo m) := #[]
  for (addr, ci) in kenv do
    items := items.push (addr, ci)
  let total := items.size
  for h : idx in [:total] do
    let (addr, ci) := items[idx]
    (← IO.getStdout).putStrLn s!"  [{idx + 1}/{total}] {ci.cv.name} ({ci.kindName})"
    (← IO.getStdout).flush
    let start ← IO.monoMsNow
    match typecheckConst kenv prims addr quotInit with
    | .ok () =>
      let elapsed := (← IO.monoMsNow) - start
      let tag := if elapsed > 100 then " ⚠ SLOW" else ""
      (← IO.getStdout).putStrLn s!"  ✓ {ci.cv.name} ({elapsed}ms){tag}"
      (← IO.getStdout).flush
    | .error e =>
      let elapsed := (← IO.monoMsNow) - start
      return .error s!"constant {ci.cv.name} ({ci.kindName}, {addr}) [{elapsed}ms]: {e}"
  return .ok ()

end Ix.Kernel
