/-
  Kernel Infer: Type inference and declaration checking.

  Environment-based kernel: types are Exprs, uses whnf/isDefEq.
-/
import Ix.Kernel.DefEq
import Ix.Kernel.Primitive

namespace Ix.Kernel

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
    | .app fn arg => .app (go fn depth) (go arg depth)
    | .lam ty body n bi => .lam (go ty depth) (go body (depth + 1)) n bi
    | .forallE ty body n bi => .forallE (go ty depth) (go body (depth + 1)) n bi
    | .letE ty val body n => .letE (go ty depth) (go val depth) (go body (depth + 1)) n
    | .proj ta idx s n => .proj ta idx (go s depth) n
    | .sort l => .sort (substLevel l)
    | .const addr lvls name => .const addr (lvls.map substLevel) name
    | _ => e

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
    | .app fn arg => .app (go fn depth) (go arg depth)
    | .lam ty body n bi => .lam (go ty depth) (go body (depth + 1)) n bi
    | .forallE ty body n bi => .forallE (go ty depth) (go body (depth + 1)) n bi
    | .letE ty val body n => .letE (go ty depth) (go val depth) (go body (depth + 1)) n
    | .proj ta idx s n => .proj ta idx (go s depth) n
    | _ => e

/-! ## Inductive validation helpers -/

/-- Check if an expression mentions a constant at the given address. -/
partial def exprMentionsConst (e : Expr m) (addr : Address) : Bool :=
  match e with
  | .const a _ _ => a == addr
  | .app fn arg => exprMentionsConst fn addr || exprMentionsConst arg addr
  | .lam ty body _ _ => exprMentionsConst ty addr || exprMentionsConst body addr
  | .forallE ty body _ _ => exprMentionsConst ty addr || exprMentionsConst body addr
  | .letE ty val body _ => exprMentionsConst ty addr || exprMentionsConst val addr || exprMentionsConst body addr
  | .proj _ _ s _ => exprMentionsConst s addr
  | _ => false

-- checkStrictPositivity and checkCtorPositivity are now monadic (inside the mutual block)
-- to allow calling whnf, matching lean4lean's checkPositivity.

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

/-! ## Type info helpers -/

def lamInfo : TypeInfo m → TypeInfo m
  | .proof => .proof
  | _ => .none

def piInfo (dom img : TypeInfo m) : TypeInfo m := match dom, img with
  | .sort lvl, .sort lvl' => .sort (Level.reduceIMax lvl lvl')
  | _, _ => .none

mutual
  /-- Infer TypeInfo from a type expression (after whnf). -/
  partial def infoFromType (typ : Expr m) : TypecheckM m (TypeInfo m) := do
    let typ' ← whnf typ
    match typ' with
    | .sort (.zero) => pure .proof
    | .sort lvl => pure (.sort lvl)
    | .app .. =>
      let head := typ'.getAppFn
      match head with
      | .const addr _ _ =>
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
    | _ => pure .none

  -- WHNF (moved from Whnf.lean to share mutual block with infer/isDefEq)

  /-- Structural WHNF: beta, let-zeta, iota-proj. No delta unfolding.
      Uses an iterative loop to avoid deep stack usage:
      - App spines are collected iteratively (not recursively)
      - Beta/let/iota/proj results loop back instead of tail-calling
      When cheapProj=true, projections are returned as-is (no struct reduction).
      When cheapRec=true, recursor applications are returned as-is (no iota reduction). -/
  partial def whnfCore (e : Expr m) (cheapRec := false) (cheapProj := false)
      : TypecheckM m (Expr m) := do
    -- Cache check FIRST — no stack cost for cache hits
    -- Context-aware: stores binding context alongside result, verified via ptr equality
    let useCache := !cheapRec && !cheapProj
    let types := (← read).types
    if useCache then
      if let some (cachedTypes, r) := (← get).whnfCoreCache.get? e then
        if unsafe ptrAddrUnsafe cachedTypes == ptrAddrUnsafe types || cachedTypes == types then
          modify fun s => { s with whnfCoreCacheHits := s.whnfCoreCacheHits + 1 }
          return r
    let r ← withRecDepthCheck (whnfCoreImpl e cheapRec cheapProj)
    if useCache then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e (types, r) }
    pure r

  partial def whnfCoreImpl (e : Expr m) (cheapRec : Bool) (cheapProj : Bool)
      : TypecheckM m (Expr m) := do
    let mut t := e
    repeat
      -- Fuel check
      let stt ← get
      if stt.fuel == 0 then throw "deep recursion fuel limit reached"
      modify fun s => { s with fuel := s.fuel - 1 }
      match t with
      | .app .. => do
        -- Collect app args iteratively (O(1) stack for app spine)
        let args := t.getAppArgs
        let fn := t.getAppFn
        let fn' ← whnfCore fn cheapRec cheapProj  -- recurse only on non-app head
        -- Beta-reduce: consume as many args as possible
        let mut result := fn'
        let mut i : Nat := 0
        while i < args.size do
          match result with
          | .lam _ body _ _ =>
            result := body.instantiate1 args[i]!
            i := i + 1
          | _ => break
        if i > 0 then
          -- Beta reductions happened. Apply remaining args and loop.
          for h : j in [i:args.size] do
            result := Expr.mkApp result args[j]!
          t := result; continue  -- loop instead of recursive tail call
        else
          -- No beta reductions. Try recursor/proj reduction.
          let e' := if fn == fn' then t else fn'.mkAppN args
          if cheapRec then return e'  -- skip recursor reduction
          let r ← tryReduceApp e'
          if r == e' then return r  -- stuck, return
          t := r; continue  -- iota/quot reduced, loop to re-process
      | .bvar idx _ => do
        -- Zeta-reduce let-bound bvars: look up the stored value and substitute
        let ctx ← read
        let depth := ctx.types.size
        if idx < depth then
          let arrayIdx := depth - 1 - idx
          if h : arrayIdx < ctx.letValues.size then
            if let some val := ctx.letValues[arrayIdx] then
              -- Shift free bvars in val past the intermediate binders
              t := val.liftBVars (idx + 1); continue
        return t
      | .letE _ val body _ =>
        t := body.instantiate1 val; continue  -- loop instead of recursion
      | .proj typeAddr idx struct _ => do
        -- cheapProj=true: try structural-only reduction (whnfCore, no delta)
        -- cheapProj=false: full reduction (whnf, with delta)
        let struct' ← if cheapProj then whnfCore struct cheapRec cheapProj else whnf struct
        match ← reduceProj typeAddr idx struct' with
        | some result => t := result; continue  -- loop instead of recursion
        | none =>
          return if struct == struct' then t else .proj typeAddr idx struct' default
      | _ => return t
    return t  -- unreachable, but needed for type checking

  /-- Try to reduce an application whose head is in WHNF.
      Handles recursor iota-reduction and quotient reduction. -/
  partial def tryReduceApp (e : Expr m) : TypecheckM m (Expr m) := do
    let fn := e.getAppFn
    match fn with
    | .const addr _ _ => do
      ensureTypedConst addr
      match (← get).typedConsts.get? addr with
      | some (.recursor _ params motives minors indices isK indAddr rules) =>
        let args := e.getAppArgs
        let majorIdx := params + motives + minors + indices
        if h : majorIdx < args.size then
          let major := args[majorIdx]
          let major' ← whnf major
          if isK then
            tryKReduction e addr args major' params motives minors indices indAddr
          else
            tryIotaReduction e addr args major' params indices indAddr rules motives minors
        else pure e
      | some (.quotient _ kind) =>
        match kind with
        | .lift => tryQuotReduction e 6 3
        | .ind  => tryQuotReduction e 5 3
        | _ => pure e
      | _ => pure e
    | _ => pure e

  /-- K-reduction: for Prop inductives with single zero-field constructor.
      Returns the (only) minor premise, plus any extra args after the major.
      When the major is not a constructor, tries toCtorWhenK: infers the major's type,
      checks it matches the inductive, and constructs the nullary constructor. -/
  partial def tryKReduction (e : Expr m) (_addr : Address) (args : Array (Expr m))
      (major : Expr m) (params motives minors indices : Nat) (indAddr : Address)
      : TypecheckM m (Expr m) := do
    -- Check if major is a constructor (including nat literal → ctor conversion)
    let ctx ← read
    let majorCtor := toCtorIfLit ctx.prims major
    let isCtor := match majorCtor.getAppFn with
      | .const ctorAddr _ _ =>
        match ctx.kenv.find? ctorAddr with
        | some (.ctorInfo _) => true
        | _ => false
      | _ => false
    if !isCtor then
      -- toCtorWhenK: verify the major's type matches the K-inductive.
      -- K-types have zero fields, so the ctor itself isn't needed — we just return the minor.
      match ← toCtorWhenK major indAddr with
      | some _ => pure ()  -- type matches, fall through to K-reduction
      | none => return e
    -- K-reduction: return the (only) minor premise
    let minorIdx := params + motives
    if h : minorIdx < args.size then
      let mut result := args[minorIdx]
      -- Apply extra args after major premise (matching lean4 kernel behavior)
      let majorIdx := params + motives + minors + indices
      if majorIdx + 1 < args.size then
        result := result.mkAppRange (majorIdx + 1) args.size args
      return result
    pure e

  /-- For K-like inductives, try to construct the nullary constructor from the major's type.
      Infers the major's type, checks it matches the inductive, and returns the constructor.
      Matches lean4lean's `toCtorWhenK` / lean4 C++ `to_cnstr_when_K`. -/
  partial def toCtorWhenK (major : Expr m) (indAddr : Address) : TypecheckM m (Option (Expr m)) := do
    let kenv := (← read).kenv
    match kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if iv.ctors.isEmpty then return none
      let ctorAddr := iv.ctors[0]!
      -- Infer major's type and check it matches the inductive
      let (_, majorType) ← try withInferOnly (infer major) catch _ => return none
      let majorType' ← whnf majorType
      let majorHead := majorType'.getAppFn
      match majorHead with
      | .const headAddr _ _ =>
        if headAddr != indAddr then return none
        -- Construct the nullary constructor applied to params from the type
        let typeArgs := majorType'.getAppArgs
        let ctorUnivs := majorHead.constLevels!
        let mut ctor : Expr m := Expr.mkConst ctorAddr ctorUnivs
        -- Apply params (first numParams args of the type)
        for i in [:iv.numParams] do
          if i < typeArgs.size then
            ctor := Expr.mkApp ctor typeArgs[i]!
        -- Verify ctor type matches major type (prevents K-reduction when indices differ)
        let (_, ctorType) ← try withInferOnly (infer ctor) catch _ => return none
        if !(← isDefEq majorType' ctorType) then return none
        return some ctor
      | _ => return none
    | _ => return none

  /-- Iota-reduction: reduce a recursor applied to a constructor.
      Follows the lean4 algorithm:
        1. Apply params + motives + minors from recursor args to rule RHS
        2. Apply constructor fields (skip constructor params) to rule RHS
        3. Apply extra args after major premise to rule RHS
      Beta reduction happens in the subsequent whnfCore call. -/
  partial def tryIotaReduction (e : Expr m) (_addr : Address) (args : Array (Expr m))
      (major : Expr m) (params indices : Nat) (indAddr : Address)
      (rules : Array (Nat × TypedExpr m))
      (motives minors : Nat) : TypecheckM m (Expr m) := do
    let prims := (← read).prims
    let majorCtor := toCtorIfLit prims major
    let majorFn := majorCtor.getAppFn
    match majorFn with
    | .const ctorAddr _ _ => do
      let kenv := (← read).kenv
      let typedConsts := (← get).typedConsts
      let ctorInfo? := match kenv.find? ctorAddr with
        | some (.ctorInfo cv) => some (cv.cidx, cv.numFields)
        | _ =>
          match typedConsts.get? ctorAddr with
          | some (.constructor _ ctorIdx numFields) => some (ctorIdx, numFields)
          | _ => none
      match ctorInfo? with
      | some (ctorIdx, _) =>
        match rules[ctorIdx]? with
        | some (nfields, rhs) =>
          let majorArgs := majorCtor.getAppArgs
          if nfields > majorArgs.size then return e
          -- Instantiate universe level params in the rule RHS
          let recFn := e.getAppFn
          let recLevels := recFn.constLevels!
          let mut result := rhs.body.instantiateLevelParams recLevels
          -- Phase 1: Apply params + motives + minors from recursor args
          let pmmEnd := params + motives + minors
          result := result.mkAppRange 0 pmmEnd args
          -- Phase 2: Apply constructor fields (skip constructor's own params)
          let ctorParamCount := majorArgs.size - nfields
          result := result.mkAppRange ctorParamCount majorArgs.size majorArgs
          -- Phase 3: Apply remaining arguments after major premise
          let majorIdx := params + motives + minors + indices
          if majorIdx + 1 < args.size then
            result := result.mkAppRange (majorIdx + 1) args.size args
          pure result  -- return raw result; whnfCore's loop will re-process
        | none => pure e
      | none =>
        -- Not a constructor, try structure eta
        tryStructEta e args params indices indAddr rules major motives minors
    | _ =>
      tryStructEta e args params indices indAddr rules major motives minors

  /-- Structure eta: expand struct-like major via projections.
      Skips Prop structures (proof irrelevance handles those; projections may not reduce). -/
  partial def tryStructEta (e : Expr m) (args : Array (Expr m))
      (params : Nat) (indices : Nat) (indAddr : Address)
      (rules : Array (Nat × TypedExpr m)) (major : Expr m)
      (motives minors : Nat) : TypecheckM m (Expr m) := do
    let kenv := (← read).kenv
    if !kenv.isStructureLike indAddr then return e
    -- Skip Prop structures: proof irrelevance handles them, projections may not reduce.
    let (_, majorType) ← try withInferOnly (infer major) catch _ => return e
    if ← (try isProp majorType catch _ => pure false) then return e
    match rules[0]? with
    | some (nfields, rhs) =>
      let recFn := e.getAppFn
      let recLevels := recFn.constLevels!
      let mut result := rhs.body.instantiateLevelParams recLevels
      -- Phase 1: params + motives + minors
      let pmmEnd := params + motives + minors
      result := result.mkAppRange 0 pmmEnd args
      -- Phase 2: projections as fields
      let mut projArgs : Array (Expr m) := #[]
      for i in [:nfields] do
        projArgs := projArgs.push (Expr.mkProj indAddr i major)
      result := projArgs.foldl (fun acc a => Expr.mkApp acc a) result
      -- Phase 3: extra args after major
      let majorIdx := params + motives + minors + indices
      if majorIdx + 1 < args.size then
        result := result.mkAppRange (majorIdx + 1) args.size args
      pure result  -- return raw result; whnfCore's loop will re-process
    | none => pure e

  /-- Quotient reduction: Quot.lift / Quot.ind.
      For Quot.lift: `@Quot.lift α r β f h q` — reduceSize=6, fPos=3 (f is at index 3)
      For Quot.ind:  `@Quot.ind α r β f q`   — reduceSize=5, fPos=3 (f is at index 3)
      When major (q) reduces to `@Quot.mk α r a`, result is `f a`. -/
  partial def tryQuotReduction (e : Expr m) (reduceSize fPos : Nat) : TypecheckM m (Expr m) := do
    let args := e.getAppArgs
    if args.size < reduceSize then return e
    let majorIdx := reduceSize - 1
    if h : majorIdx < args.size then
      let major := args[majorIdx]
      let major' ← whnf major
      let majorFn := major'.getAppFn
      match majorFn with
      | .const majorAddr _ _ =>
        ensureTypedConst majorAddr
        match (← get).typedConsts.get? majorAddr with
        | some (.quotient _ .ctor) =>
          let majorArgs := major'.getAppArgs
          -- Quot.mk has 3 args: [α, r, a]. The data 'a' is the last one.
          if majorArgs.size < 3 then throw "Quot.mk should have at least 3 args"
          let dataArg := majorArgs[majorArgs.size - 1]!
          if h2 : fPos < args.size then
            let f := args[fPos]
            let result := Expr.mkApp f dataArg
            -- Apply any extra args after the major premise
            let result := if majorIdx + 1 < args.size then
              result.mkAppRange (majorIdx + 1) args.size args
            else result
            pure result  -- return raw result; whnfCore's loop will re-process
          else return e
        | _ => return e
      | _ => return e
    else return e

  /-- Try to reduce a Nat primitive, whnf'ing args if needed (like lean4lean's reduceNat).
      Inside the mutual block so it can call `whnf` on arguments.
      Handles both `.lit (.natVal n)` and `Nat.zero` constructor forms,
      matching lean4lean's `rawNatLitExt?`. -/
  partial def tryReduceNat (e : Expr m) : TypecheckM m (Option (Expr m)) := do
    let fn := e.getAppFn
    match fn with
    | .const addr _ _ =>
      let prims := (← read).prims
      if !isPrimOp prims addr then return none
      let args := e.getAppArgs
      -- Nat.succ: 1 arg
      if addr == prims.natSucc then
        if args.size >= 1 then
          let a ← whnf args[0]!
          match extractNatVal prims a with
          | some n => return some (.lit (.natVal (n + 1)))
          | none => return none
        else return none
      -- Binary nat operations: 2 args, whnf both (matches lean4lean reduceBinNatOp)
      else if args.size >= 2 then
        let a ← whnf args[0]!
        let b ← whnf args[1]!
        match extractNatVal prims a, extractNatVal prims b with
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

  /-- Evaluate a native reduction marker (`Lean.reduceBool c` or `Lean.reduceNat c`).
      Looks up the target constant's definition and fully reduces it via `whnf`
      to extract the Bool/Nat result. This is the whnf-based fallback for
      `native_decide`; a CEK machine evaluator would be faster for complex proofs. -/
  partial def reduceNativeExpr (t : Expr m) : TypecheckM m (Option (Expr m)) := do
    let prims := (← read).prims
    let kenv := (← read).kenv
    -- Expression shape: app (const reduceBool/reduceNat []) (const targetDef [])
    let .app fn constArg := t | return none
    let .const fnAddr _ _ := fn | return none
    let .const defAddr _ _ := constArg | return none
    let isReduceBool := fnAddr == prims.reduceBool
    let isReduceNat := fnAddr == prims.reduceNat
    if !isReduceBool && !isReduceNat then return none
    match kenv.find? defAddr with
    | some (.defnInfo dv) =>
      let result ← whnf dv.value
      if isReduceBool then
        if result.isConstOf prims.boolTrue then
          return some (Expr.mkConst prims.boolTrue #[])
        else if result.isConstOf prims.boolFalse then
          return some (Expr.mkConst prims.boolFalse #[])
        else throw s!"reduceBool: constant did not reduce to Bool.true or Bool.false"
      else -- isReduceNat
        match extractNatVal prims result with
        | some n => return some (.lit (.natVal n))
        | none => throw s!"reduceNat: constant did not reduce to a Nat literal"
    | _ => throw s!"reduceNative: target is not a definition"

  partial def whnf (e : Expr m) : TypecheckM m (Expr m) := do
    -- Trivially-irreducible expressions: return immediately (no fuel/depth cost)
    match e with
    | .sort .. | .forallE .. | .lit .. => return e
    | .bvar idx _ =>
      -- BVar is irreducible unless let-bound (zeta-reduction needed)
      let ctx ← read
      let depth := ctx.types.size
      if idx < depth then
        let arrayIdx := depth - 1 - idx
        if h : arrayIdx < ctx.letValues.size then
          if ctx.letValues[arrayIdx].isNone then return e
      else return e  -- out-of-range bvar, can't reduce
    | _ => pure ()
    -- Cache check — no fuel or stack cost for cache hits
    -- Context-aware: stores binding context alongside result, verified via ptr equality
    let types := (← read).types
    if let some (cachedTypes, r) := (← get).whnfCache.get? e then
      if unsafe ptrAddrUnsafe cachedTypes == ptrAddrUnsafe types || cachedTypes == types then
        modify fun s => { s with whnfCacheHits := s.whnfCacheHits + 1 }
        return r
    modify fun s => { s with whnfCalls := s.whnfCalls + 1 }
    withRecDepthCheck do
    withFuelCheck do
    let r ← whnfImpl e
    modify fun s => { s with whnfCache := s.whnfCache.insert e (types, r) }
    pure r

  partial def whnfImpl (e : Expr m) : TypecheckM m (Expr m) := do
    -- Use cheapProj=true so projections are deferred to the iterative chain handler below.
    -- This avoids O(depth) recursive whnf calls for nested projections like a.b.c.d.
    let mut t ← whnfCore e (cheapProj := true)
    let mut steps := 0
    repeat
      if steps > 10000 then throw "whnf delta step limit (10000) exceeded"
      -- Try native reduction (reduceBool/reduceNat markers)
      -- These are @[extern] constants used by native_decide. When we see
      -- `Lean.reduceBool c` or `Lean.reduceNat c`, look up c's definition
      -- and fully reduce it via whnf to extract the Bool/Nat result.
      let prims := (← read).prims
      if prims.reduceBool != default || prims.reduceNat != default then
        if let some r ← reduceNativeExpr t then
          t ← whnfCore r (cheapProj := true); steps := steps + 1; continue
      -- Try nat primitive reduction (whnf's args like lean4lean's reduceNat)
      if let some r := ← tryReduceNat t then
        t ← whnfCore r (cheapProj := true); steps := steps + 1; continue
      -- Handle projections iteratively: flatten nested projection chains
      -- and resolve from inside out with a single whnf call on the innermost struct.
      match t.getAppFn with
      | .proj _ _ _ _ =>
        -- Collect the projection chain from outside in
        let mut projStack : Array (Address × Nat × Array (Expr m)) := #[]
        let mut inner := t
        repeat
          match inner.getAppFn with
          | .proj typeAddr idx struct _ =>
            projStack := projStack.push (typeAddr, idx, inner.getAppArgs)
            inner := struct
          | _ => break
        -- Reduce the innermost struct with depth-guarded whnf
        let innerReduced ← whnf inner
        -- Resolve projections from inside out (last pushed = innermost)
        let mut current := innerReduced
        let mut allResolved := true
        let mut i := projStack.size
        while i > 0 do
          i := i - 1
          let (typeAddr, idx, args) := projStack[i]!
          match ← reduceProj typeAddr idx current with
          | some result =>
            let applied := if args.isEmpty then result else result.mkAppN args
            current ← whnfCore applied (cheapProj := true)
          | none =>
            -- This projection couldn't be resolved. Reconstruct remaining chain.
            let stuck := if args.isEmpty then
              Expr.mkProj typeAddr idx current
            else
              (Expr.mkProj typeAddr idx current).mkAppN args
            current ← whnfCore stuck (cheapProj := true)
            -- Reconstruct outer projections
            while i > 0 do
              i := i - 1
              let (ta, ix, as) := projStack[i]!
              current := if as.isEmpty then
                Expr.mkProj ta ix current
              else
                (Expr.mkProj ta ix current).mkAppN as
            allResolved := false
            break
        if allResolved || current != t then
          t := current; steps := steps + 1; continue
      | _ => pure ()
      -- Try delta unfolding
      if let some r := ← unfoldDefinition t then
        t ← whnfCore r (cheapProj := true); steps := steps + 1; continue
      break
    pure t

  /-- Unfold a single delta step (definition body). -/
  partial def unfoldDefinition (e : Expr m) : TypecheckM m (Option (Expr m)) := do
    let head := e.getAppFn
    match head with
    | .const addr levels _ => do
      let ci ← derefConst addr
      match ci with
      | .defnInfo v =>
        if levels.size != v.numLevels then return none
        let body := v.value.instantiateLevelParams levels
        return some (body.mkAppN (e.getAppArgs))
      | .thmInfo v =>
        if levels.size != v.numLevels then return none
        let body := v.value.instantiateLevelParams levels
        return some (body.mkAppN (e.getAppArgs))
      | _ => return none
    | _ => return none

  -- Type Inference and Checking

  /-- Check that a term has a given type. -/
  partial def check (term : Expr m) (expectedType : Expr m) : TypecheckM m (TypedExpr m) := do
    -- if (← read).trace then dbg_trace s!"check: {term.tag}"
    let (te, inferredType) ← infer term
    if !(← isDefEq inferredType expectedType) then
      let ppInferred := inferredType.pp
      let ppExpected := expectedType.pp
      throw s!"Type mismatch on {term.tag}\n  inferred: {ppInferred}\n  expected: {ppExpected}"
    pure te

  /-- Infer the type of an expression, returning the typed expression and its type. -/
  partial def infer (term : Expr m) : TypecheckM m (TypedExpr m × Expr m) := do
    -- Check infer cache FIRST — no fuel or stack cost for cache hits
    let types := (← read).types
    if let some (cachedCtx, cachedInfo, cachedType) := (← get).inferCache.get? term then
      -- Ptr equality first, structural BEq fallback
      -- For consts/sorts/lits, context doesn't matter (always closed)
      let contextOk := match term with
        | .const .. | .sort .. | .lit .. => true
        | _ => unsafe ptrAddrUnsafe cachedCtx == ptrAddrUnsafe types || cachedCtx == types
      if contextOk then
        modify fun s => { s with inferCacheHits := s.inferCacheHits + 1 }
        let te : TypedExpr m := ⟨cachedInfo, term⟩
        return (te, cachedType)
    modify fun s => { s with inferCalls := s.inferCalls + 1 }
    withRecDepthCheck do
    withFuelCheck do
    let result ← do match term with
      | .bvar idx bvarName => do
        let ctx ← read
        let depth := ctx.types.size
        if idx < depth then
          let arrayIdx := depth - 1 - idx
          if h : arrayIdx < ctx.types.size then
            let rawType := ctx.types[arrayIdx]
            let typ := rawType.liftBVars (idx + 1)
            let te : TypedExpr m := ⟨← infoFromType typ, .bvar idx bvarName⟩
            pure (te, typ)
          else
            throw s!"var@{idx} out of environment range (size {ctx.types.size})"
        else
          match ctx.mutTypes.get? (idx - depth) with
          | some (addr, typeExprFn) =>
            if some addr == ctx.recAddr? then
              throw s!"Invalid recursion"
            let univs := Array.ofFn (n := 0) fun i => Level.param i.val (default : MetaField m Ix.Name)
            let typ := typeExprFn univs
            let name ← lookupName addr
            let te : TypedExpr m := ⟨← infoFromType typ, .const addr univs name⟩
            pure (te, typ)
          | none =>
            throw s!"var@{idx} out of environment range and does not represent a mutual constant"
      | .sort lvl => do
        let lvl' := Level.succ lvl
        let typ := Expr.mkSort lvl'
        let te : TypedExpr m := ⟨.sort lvl', .sort lvl⟩
        pure (te, typ)
      | .app .. => do
        -- Flatten app spine to avoid O(num_args) stack depth
        let args := term.getAppArgs
        let fn := term.getAppFn
        let (fnTe, fncType) ← infer fn
        let mut currentType := fncType
        let mut resultBody := fnTe.body
        let inferOnly := (← read).inferOnly
        for h : i in [:args.size] do
          let arg := args[i]
          let currentType' ← whnf currentType
          match currentType' with
          | .forallE dom body _ _ => do
            if inferOnly then
              resultBody := Expr.mkApp resultBody arg
            else
              let argTe ← check arg dom
              resultBody := Expr.mkApp resultBody argTe.body
            currentType := body.instantiate1 arg
          | _ =>
            throw s!"Expected a pi type, got {currentType'.pp}\n  function: {fn.pp}\n  arg #{i}: {arg.pp}"
        let te : TypedExpr m := ⟨← infoFromType currentType, resultBody⟩
        pure (te, currentType)
      | .lam .. => do
        -- Iterate lambda chain to avoid O(n) stack depth
        let inferOnly := (← read).inferOnly
        let mut cur := term
        let mut extTypes := (← read).types
        let mut extLetValues := (← read).letValues
        let mut binderMeta : Array (Expr m × Expr m × MetaField m Ix.Name × MetaField m Lean.BinderInfo) := #[]
        repeat
          match cur with
          | .lam ty body lamName lamBi =>
            let domBody ← if inferOnly then pure ty
              else do let (te, _) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isSort ty); pure te.body
            binderMeta := binderMeta.push (domBody, ty, lamName, lamBi)
            extTypes := extTypes.push ty
            extLetValues := extLetValues.push none
            cur := body
          | _ => break
        let (bodTe, imgType) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (infer cur)
        let mut resultType := imgType
        let mut resultBody := bodTe.body
        let mut resultInfo := bodTe.info
        for i in [:binderMeta.size] do
          let j := binderMeta.size - 1 - i
          let (domBody, origTy, lamName, lamBi) := binderMeta[j]!
          resultType := .forallE origTy resultType lamName default
          resultBody := .lam domBody resultBody lamName lamBi
          resultInfo := lamInfo resultInfo
        pure (⟨resultInfo, resultBody⟩, resultType)
      | .forallE .. => do
        -- Iterate forallE chain to avoid O(n) stack depth
        let mut cur := term
        let mut extTypes := (← read).types
        let mut extLetValues := (← read).letValues
        let mut binderMeta : Array (Expr m × Level m × MetaField m Ix.Name) := #[]
        repeat
          match cur with
          | .forallE ty body piName _ =>
            let (domTe, domLvl) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isSort ty)
            binderMeta := binderMeta.push (domTe.body, domLvl, piName)
            extTypes := extTypes.push ty
            extLetValues := extLetValues.push none
            cur := body
          | _ => break
        let (imgTe, imgLvl) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isSort cur)
        let mut resultLvl := imgLvl
        let mut resultBody := imgTe.body
        for i in [:binderMeta.size] do
          let j := binderMeta.size - 1 - i
          let (domBody, domLvl, piName) := binderMeta[j]!
          resultLvl := Level.reduceIMax domLvl resultLvl
          resultBody := .forallE domBody resultBody piName default
        let typ := Expr.mkSort resultLvl
        pure (⟨← infoFromType typ, resultBody⟩, typ)
      | .letE .. => do
        -- Iterate let chain to avoid O(n) stack depth
        let inferOnly := (← read).inferOnly
        let mut cur := term
        let mut extTypes := (← read).types
        let mut extLetValues := (← read).letValues
        let mut extNumLets := (← read).numLetBindings
        let mut binderInfo : Array (Expr m × Expr m × Expr m × MetaField m Ix.Name) := #[]
        repeat
          match cur with
          | .letE ty val body letName =>
            if inferOnly then
              binderInfo := binderInfo.push (ty, val, val, letName)
            else
              let (tyTe, _) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, numLetBindings := extNumLets }) (isSort ty)
              let valTe ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, numLetBindings := extNumLets }) (check val ty)
              binderInfo := binderInfo.push (tyTe.body, valTe.body, val, letName)
            extTypes := extTypes.push ty
            extLetValues := extLetValues.push (some val)
            extNumLets := extNumLets + 1
            cur := body
          | _ => break
        let (bodTe, bodType) ← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues, numLetBindings := extNumLets }) (infer cur)
        let mut resultType := bodType.cheapBetaReduce
        let mut resultBody := bodTe.body
        for i in [:binderInfo.size] do
          let j := binderInfo.size - 1 - i
          let (tyBody, valBody, origVal, letName) := binderInfo[j]!
          resultType := resultType.instantiate1 origVal
          resultBody := .letE tyBody valBody resultBody letName
        pure (⟨bodTe.info, resultBody⟩, resultType)
      | .lit (.natVal _) => do
        let prims := (← read).prims
        let typ := Expr.mkConst prims.nat #[]
        let te : TypedExpr m := ⟨.none, term⟩
        pure (te, typ)
      | .lit (.strVal _) => do
        let prims := (← read).prims
        let typ := Expr.mkConst prims.string #[]
        let te : TypedExpr m := ⟨.none, term⟩
        pure (te, typ)
      | .const addr constUnivs _ => do
        ensureTypedConst addr
        -- Safety check: safe declarations cannot reference unsafe/partial constants
        let inferOnly := (← read).inferOnly
        if !inferOnly then
          let ci ← derefConst addr
          let curSafety := (← read).safety
          if ci.isUnsafe && curSafety != .unsafe then
            throw s!"invalid declaration, it uses unsafe declaration {addr}"
          if let .defnInfo v := ci then
            if v.safety == .partial && curSafety == .safe then
              throw s!"invalid declaration, safe declaration must not contain partial declaration {addr}"
          -- Universe level param count validation
          if constUnivs.size != ci.numLevels then
            throw s!"incorrect number of universe levels for {addr}: expected {ci.numLevels}, got {constUnivs.size}"
        match (← get).constTypeCache.get? addr with
        | some (cachedUnivs, cachedTyp) =>
          if cachedUnivs == constUnivs then
            let te : TypedExpr m := ⟨← infoFromType cachedTyp, term⟩
            pure (te, cachedTyp)
          else
            let tconst ← derefTypedConst addr
            let typ := tconst.type.body.instantiateLevelParams constUnivs
            modify fun stt => { stt with constTypeCache := stt.constTypeCache.insert addr (constUnivs, typ) }
            let te : TypedExpr m := ⟨← infoFromType typ, term⟩
            pure (te, typ)
        | none =>
          let tconst ← derefTypedConst addr
          let typ := tconst.type.body.instantiateLevelParams constUnivs
          modify fun stt => { stt with constTypeCache := stt.constTypeCache.insert addr (constUnivs, typ) }
          let te : TypedExpr m := ⟨← infoFromType typ, term⟩
          pure (te, typ)
      | .proj typeAddr idx struct _ => do
        let (structTe, structType) ← infer struct
        let (ctorType, ctorUnivs, numParams, params) ← getStructInfo structType
        let mut ct := ctorType.instantiateLevelParams ctorUnivs
        for _ in [:numParams] do
          ct ← whnf ct
          match ct with
          | .forallE _ body _ _ => ct := body
          | _ => throw "Structure constructor has too few parameters"
        ct := ct.instantiate params.reverse
        for i in [:idx] do
          ct ← whnf ct
          match ct with
          | .forallE _ body _ _ =>
            let projExpr := Expr.mkProj typeAddr i structTe.body
            ct := body.instantiate1 projExpr
          | _ => throw "Structure type does not have enough fields"
        ct ← whnf ct
        match ct with
        | .forallE dom _ _ _ =>
          let te : TypedExpr m := ⟨← infoFromType dom, .proj typeAddr idx structTe.body default⟩
          pure (te, dom)
        | _ => throw "Impossible case: structure type does not have enough fields"
    -- Cache the inferred type and TypeInfo with the binding context
    modify fun stt => { stt with inferCache := stt.inferCache.insert term (types, result.1.info, result.2) }
    pure result

  /-- Check if an expression is a Sort, returning the typed expr and the universe level. -/
  partial def isSort (expr : Expr m) : TypecheckM m (TypedExpr m × Level m) := do
    let (te, typ) ← infer expr
    let typ' ← whnf typ
    match typ' with
    | .sort u => pure (te, u)
    | _ =>
      throw s!"Expected a sort type, got {typ'.pp}\n  expr: {expr.pp}"

  /-- Get structure info from a type that should be a structure.
      Returns (constructor type expr, universe levels, numParams, param exprs). -/
  partial def getStructInfo (structType : Expr m) :
      TypecheckM m (Expr m × Array (Level m) × Nat × Array (Expr m)) := do
    let structType' ← whnf structType
    let fn := structType'.getAppFn
    match fn with
    | .const indAddr univs _ =>
      match (← read).kenv.find? indAddr with
      | some (.inductInfo v) =>
        let params := structType'.getAppArgs
        if v.ctors.size != 1 || params.size != v.numParams then
          throw s!"Expected a structure type, but {v.name} ({indAddr}) has {v.ctors.size} ctors and {params.size}/{v.numParams} params"
        ensureTypedConst indAddr
        let ctorAddr := v.ctors[0]!
        ensureTypedConst ctorAddr
        match (← get).typedConsts.get? ctorAddr with
        | some (.constructor type _ _) =>
          return (type.body, univs, v.numParams, params)
        | _ => throw s!"Constructor {ctorAddr} is not in typed consts"
      | some ci => throw s!"Expected a structure type, but {indAddr} is a {ci.kindName}"
      | none => throw s!"Expected a structure type, but {indAddr} not found in env"
    | _ =>
      throw s!"Expected a structure type, got {structType'.pp}"

  /-- Typecheck a constant. -/
  partial def checkConst (addr : Address) : TypecheckM m Unit := withResetCtx do
    -- Determine safety early for withSafety wrapper
    let ci? := (← read).kenv.find? addr
    let declSafety := match ci? with | some ci => ci.safety | none => .safe
    withSafety declSafety do
    -- Reset fuel and per-constant caches
    modify fun stt => { stt with
      constTypeCache := {},
      whnfCache := {},
      whnfCoreCache := {},
      inferCache := {},
      eqvManager := {},
      failureCache := {},
      fuel := defaultFuel,
      recDepth := 0,
      maxRecDepth := 0
    }
    -- Skip if already in typedConsts
    if (← get).typedConsts.get? addr |>.isSome then
      return ()
    let ci ← derefConst addr
    let univs := ci.cv.mkUnivParams
    let newConst ← match ci with
      | .axiomInfo _ =>
        let (type, _) ← isSort ci.type
        pure (TypedConst.axiom type)
      | .opaqueInfo _ =>
        let (type, _) ← isSort ci.type
        let value ← withRecAddr addr (check ci.value?.get! type.body)
        pure (TypedConst.opaque type value)
      | .thmInfo _ =>
        let (type, lvl) ← withInferOnly (isSort ci.type)
        if !Level.isZero lvl then
          throw s!"theorem type must be a proposition (Sort 0)"
        let (_, valType) ← withRecAddr addr (withInferOnly (infer ci.value?.get!))
        if !(← withInferOnly (isDefEq valType type.body)) then
          throw s!"theorem value type doesn't match declared type"
        let value : TypedExpr m := ⟨.proof, ci.value?.get!⟩
        pure (TypedConst.theorem type value)
      | .defnInfo v =>
        let (type, _) ← isSort ci.type
        let part := v.safety == .partial
        let value ←
          if part then
            let typExpr := type.body
            let mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → Expr m)) compare :=
              (Std.TreeMap.empty).insert 0 (addr, fun _ => typExpr)
            withMutTypes mutTypes (withRecAddr addr (check v.value type.body))
          else withRecAddr addr (check v.value type.body)
        validatePrimitive addr
        pure (TypedConst.definition type value part)
      | .quotInfo v =>
        let (type, _) ← isSort ci.type
        if (← read).quotInit then
          validateQuotient
        pure (TypedConst.quotient type v.kind)
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
          validateKFlag v indAddr
        validateRecursorRules v indAddr
        checkElimLevel ci.type v indAddr
        -- Check each rule RHS has the expected type
        match (← read).kenv.find? indAddr with
        | some (.inductInfo iv) =>
          for h : i in [:v.rules.size] do
            let rule := v.rules[i]
            if i < iv.ctors.size then
              checkRecursorRuleType ci.type v iv.ctors[i]! rule.nfields rule.rhs
        | _ => pure ()
        let typedRules ← v.rules.mapM fun rule => do
          let (rhs, _) ← infer rule.rhs
          pure (rule.nfields, rhs)
        pure (TypedConst.recursor type v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules)
    modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr newConst }

  /-- Walk a Pi chain to extract the return sort level. -/
  partial def getReturnSort (expr : Expr m) (numBinders : Nat) : TypecheckM m (Level m) :=
    match numBinders, expr with
    | 0, .sort u => pure u
    | 0, _ => do
      let (_, typ) ← infer expr
      let typ' ← whnf typ
      match typ' with
      | .sort u => pure u
      | _ => throw "inductive return type is not a sort"
    | n+1, .forallE dom body _ _ => do
      let _ ← isSort dom
      withExtendedCtx dom (getReturnSort body n)
    | _, _ => throw "inductive type has fewer binders than expected"

  /-- Check that the fields of a nested inductive's constructor use the current
      inductives only in positive positions. Walks past numParams binders of the
      outer ctor type, substituting actual param args, then checks each field. -/
  partial def checkNestedCtorFields (ctorType : Expr m) (numParams : Nat)
      (paramArgs : Array (Expr m)) (indAddrs : Array Address) : TypecheckM m Bool := do
    -- Walk past param binders to get the field portion of the ctor type
    let mut ty := ctorType
    for _ in [:numParams] do
      match ty with
      | .forallE _ body _ _ => ty := body
      | _ => return true
    -- Substitute all param bvars: bvar 0 = last param, bvar (n-1) = first param
    ty := ty.instantiate paramArgs.reverse
    -- Check each field for positivity
    loop ty
  where
    loop (ty : Expr m) : TypecheckM m Bool := do
      let ty ← whnf ty
      match ty with
      | .forallE dom body _ _ =>
        if !(← checkPositivity dom indAddrs) then return false
        loop body
      | _ => return true

  /-- Check strict positivity of a field type w.r.t. a set of inductive addresses.
      Handles direct recursion, negative-position rejection, and nested inductives
      (where the inductive appears as a param of a previously-defined inductive). -/
  partial def checkPositivity (ty : Expr m) (indAddrs : Array Address) : TypecheckM m Bool := do
    let ty ← whnf ty
    if !indAddrs.any (exprMentionsConst ty ·) then return true
    match ty with
    | .forallE dom body _ _ =>
      if indAddrs.any (exprMentionsConst dom ·) then
        return false
      checkPositivity body indAddrs
    | e =>
      let fn := e.getAppFn
      match fn with
      | .const addr _ _ =>
        if indAddrs.any (· == addr) then return true
        -- Nested inductive: head is a previously-defined inductive
        match (← read).kenv.find? addr with
        | some (.inductInfo fv) =>
          if fv.isUnsafe then return false
          let args := e.getAppArgs
          -- Index args must not mention current inductives
          for i in [fv.numParams:args.size] do
            if indAddrs.any (exprMentionsConst args[i]! ·) then return false
          -- Check all constructors of the outer inductive use params positively.
          -- Augment indAddrs with the outer inductive's own addresses so that
          -- its self-recursive fields (e.g., List α in List.cons) are accepted
          -- immediately rather than causing infinite recursion.
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

  /-- Walk a Pi chain, skip numParams binders, then check positivity of each field.
      Monadic to call whnf, matching lean4lean. -/
  partial def checkCtorFields (ctorType : Expr m) (numParams : Nat) (indAddrs : Array Address)
      : TypecheckM m (Option String) :=
    go ctorType numParams
  where
    go (ty : Expr m) (remainingParams : Nat) : TypecheckM m (Option String) := do
      let ty ← whnf ty
      match ty with
      | .forallE _dom body _name _bi =>
        if remainingParams > 0 then
          go body (remainingParams - 1)
        else
          let domain := ty.bindingDomain!
          if !(← checkPositivity domain indAddrs) then
            return some "inductive occurs in negative position (strict positivity violation)"
          go body 0
      | _ => return none

  /-- Typecheck a mutual inductive block. -/
  partial def checkIndBlock (addr : Address) : TypecheckM m Unit := do
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
    modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr (TypedConst.inductive type isStruct) }
    let indAddrs := iv.all
    let indResultLevel := getIndResultLevel iv.type
    for (ctorAddr, _cidx) in iv.ctors.toList.zipIdx do
      match (← read).kenv.find? ctorAddr with
      | some (.ctorInfo cv) => do
        let (ctorType, _) ← isSort cv.type
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert ctorAddr (TypedConst.constructor ctorType cv.cidx cv.numFields) }
        if cv.numParams != iv.numParams then
          throw s!"Constructor {ctorAddr} has {cv.numParams} params but inductive has {iv.numParams}"
        -- Validate constructor parameter domains match inductive parameter domains
        if !iv.isUnsafe then do
          let mut indTy := iv.type
          let mut ctorTy := cv.type
          for i in [:iv.numParams] do
            match indTy, ctorTy with
            | .forallE indDom indBody _ _, .forallE ctorDom ctorBody _ _ =>
              if !(← isDefEq indDom ctorDom) then
                throw s!"Constructor {ctorAddr} parameter {i} domain doesn't match inductive parameter domain"
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
          let retType := getCtorReturnType cv.type cv.numParams cv.numFields
          -- Validate return type head is one of the inductives being defined
          let retHead := retType.getAppFn
          match retHead with
          | .const retAddr _ _ =>
            if !indAddrs.any (· == retAddr) then
              throw s!"Constructor {ctorAddr} return type head is not the inductive being defined"
          | _ =>
            throw s!"Constructor {ctorAddr} return type is not an inductive application"
          let args := retType.getAppArgs
          -- Validate param args are correct bvars (bvar (numFields + numParams - 1 - i) for param i)
          for i in [:iv.numParams] do
            if i < args.size then
              let expectedBvar := cv.numFields + iv.numParams - 1 - i
              match args[i]! with
              | .bvar idx _ =>
                if idx != expectedBvar then
                  throw s!"Constructor {ctorAddr} return type has wrong parameter at position {i}"
              | _ =>
                throw s!"Constructor {ctorAddr} return type parameter {i} is not a bound variable"
          -- Validate index args don't mention the inductives
          for i in [iv.numParams:args.size] do
            for indAddr in indAddrs do
              if exprMentionsConst args[i]! indAddr then
                throw s!"Constructor {ctorAddr} index argument mentions the inductive (unsound)"
      | _ => throw s!"Constructor {ctorAddr} not found"

  /-- Check that constructor field types have sorts <= the inductive's result sort. -/
  partial def checkFieldUniverses (ctorType : Expr m) (numParams : Nat)
      (ctorAddr : Address) (indLvl : Level m) : TypecheckM m Unit :=
    go ctorType numParams
  where
    go (ty : Expr m) (remainingParams : Nat) : TypecheckM m Unit := do
      let ty ← whnf ty
      match ty with
      | .forallE dom body _piName _ =>
        if remainingParams > 0 then do
          let _ ← isSort dom
          withExtendedCtx dom (go body (remainingParams - 1))
        else do
          let (_, fieldSortLvl) ← isSort dom
          let fieldReduced := Level.reduce fieldSortLvl
          let indReduced := Level.reduce indLvl
          if !Level.leq fieldReduced indReduced 0 && !Level.isZero indReduced then
            throw s!"Constructor {ctorAddr} field type lives in a universe larger than the inductive's universe"
          withExtendedCtx dom (go body 0)
      | _ => pure ()

  /-- Check if a single-ctor Prop inductive allows large elimination.
      All non-Prop fields must appear directly as index arguments in the return type.
      Matches lean4lean's `isLargeEliminator` / lean4 C++ `elim_only_at_universe_zero`. -/
  partial def checkLargeElimSingleCtor (ctorType : Expr m) (numParams numFields : Nat)
      : TypecheckM m Bool :=
    go ctorType numParams numFields #[]
  where
    go (ty : Expr m) (remainingParams : Nat) (remainingFields : Nat)
       (nonPropBvars : Array Nat) : TypecheckM m Bool := do
      let ty ← whnf ty
      match ty with
      | .forallE dom body _ _ =>
        if remainingParams > 0 then
          withExtendedCtx dom (go body (remainingParams - 1) remainingFields nonPropBvars)
        else if remainingFields > 0 then
          let (_, fieldSortLvl) ← isSort dom
          let nonPropBvars := if !Level.isZero fieldSortLvl then
            -- After all remaining fields, this field is bvar (remainingFields - 1)
            nonPropBvars.push (remainingFields - 1)
          else nonPropBvars
          withExtendedCtx dom (go body 0 (remainingFields - 1) nonPropBvars)
        else pure true
      | _ =>
        if nonPropBvars.isEmpty then return true
        let args := ty.getAppArgs
        for bvarIdx in nonPropBvars do
          let mut found := false
          for i in [numParams:args.size] do
            match args[i]! with
            | .bvar idx _ => if idx == bvarIdx then found := true
            | _ => pure ()
          if !found then return false
        return true

  /-- Validate that the recursor's elimination level is appropriate for the inductive.
      If the inductive doesn't allow large elimination, the motive must return Prop. -/
  partial def checkElimLevel (recType : Expr m) (rec : RecursorVal m) (indAddr : Address)
      : TypecheckM m Unit := do
    let kenv := (← read).kenv
    match kenv.find? indAddr with
    | some (.inductInfo iv) =>
      let some indLvl := getIndResultLevel iv.type | return ()
      -- Non-zero result level → large elimination always allowed
      if levelIsNonZero indLvl then return ()
      -- Extract motive sort from recursor type
      let some motiveSort := getMotiveSort recType rec.numParams | return ()
      -- If motive is already Prop, nothing to check
      if Level.isZero motiveSort then return ()
      -- Motive wants non-Prop elimination. Check if it's allowed.
      -- Mutual inductives in Prop → no large elimination
      if iv.all.size != 1 then
        throw s!"recursor claims large elimination but mutual Prop inductive only allows Prop elimination"
      if iv.ctors.isEmpty then return ()  -- empty Prop type can eliminate into any Sort
      if iv.ctors.size != 1 then
        throw s!"recursor claims large elimination but Prop inductive with multiple constructors only allows Prop elimination"
      let ctorAddr := iv.ctors[0]!
      match kenv.find? ctorAddr with
      | some (.ctorInfo cv) =>
        let allowed ← checkLargeElimSingleCtor cv.type iv.numParams cv.numFields
        if !allowed then
          throw s!"recursor claims large elimination but inductive has non-Prop fields not appearing in indices"
      | _ => return ()
    | _ => return ()

  /-- Validate K-flag: requires non-mutual, Prop, single ctor, zero fields. -/
  partial def validateKFlag (rec : RecursorVal m) (indAddr : Address) : TypecheckM m Unit := do
    match (← read).kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if iv.all.size != 1 then
        throw "recursor claims K but inductive is mutual"
      match getIndResultLevel iv.type with
      | some lvl =>
        if levelIsNonZero lvl then
          throw s!"recursor claims K but inductive is not in Prop"
      | none => throw "recursor claims K but cannot determine inductive's result sort"
      if iv.ctors.size != 1 then
        throw s!"recursor claims K but inductive has {iv.ctors.size} constructors (need 1)"
      match (← read).kenv.find? iv.ctors[0]! with
      | some (.ctorInfo cv) =>
        if cv.numFields != 0 then
          throw s!"recursor claims K but constructor has {cv.numFields} fields (need 0)"
      | _ => throw "recursor claims K but constructor not found"
    | _ => throw s!"recursor claims K but {indAddr} is not an inductive"

  /-- Validate recursor rules: check rule count, ctor membership, field counts.
      Uses `indAddr` (from getMajorInduct) to look up the inductive directly,
      since rec.all may be empty for recursor-only Ixon blocks.
      Does NOT check numParams/numIndices — auxiliary recursors (rec_1, etc.)
      can have different param counts than the major inductive. -/
  partial def validateRecursorRules (rec : RecursorVal m) (indAddr : Address) : TypecheckM m Unit := do
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
      Builds the expected type from the recursor type and constructor type,
      then verifies the inferred RHS type matches via isDefEq.
      The expected type for rule j (constructor ctor_j with nf fields) is:
        Π (rec_params) (motives) (minors) (ctor_fields) . motive indices (ctor_j params fields)
      where the first (np+nm+nk) Pi binders come from the recursor type and
      the field binders come from the constructor type (with param bvars shifted
      to skip motive/minor binders). -/
  partial def checkRecursorRuleType (recType : Expr m) (rec : RecursorVal m)
      (ctorAddr : Address) (nf : Nat) (ruleRhs : Expr m) : TypecheckM m Unit := do
    let np := rec.numParams
    let nm := rec.numMotives
    let nk := rec.numMinors
    let shift := nm + nk
    -- Look up constructor info
    let ctorCi ← derefConst ctorAddr
    let ctorType := ctorCi.type
    -- 1. Extract recursor binder domains (params + motives + minors)
    let mut recTy := recType
    let mut recDoms : Array (Expr m) := #[]
    for _ in [:np + nm + nk] do
      match recTy with
      | .forallE dom body _ _ =>
        recDoms := recDoms.push dom
        recTy := body
      | _ => throw "recursor type has too few Pi binders for params+motives+minors"
    -- Determine motive position from recursor return type.
    -- After stripping indices+major, the return expr head is bvar(ni+nk+nm-d)
    -- where d is the motive index for the major inductive.
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
    -- 2. Extract field domains from ctor type and handle nested params.
    -- The constructor may have more params than the recursor (nested inductive pattern):
    -- rec.numParams = shared params; cv.numParams may include extra "nested" params.
    let cnp := match ctorCi with | .ctorInfo cv => cv.numParams | _ => np
    -- Extract the major premise domain (needed for nested param values and level extraction).
    -- recTy (after stripping np+nm+nk) = Π (indices) (major : IndType args), ret
    let majorPremiseDom : Option (Expr m) := Id.run do
      let mut ty := recTy
      for _ in [:ni] do
        match ty with
        | .forallE _ body _ _ => ty := body
        | _ => return none
      match ty with
      | .forallE dom _ _ _ => return some dom
      | _ => return none
    -- Compute constructor level substitution.
    -- For nested inductives (cnp > np): extract actual levels from the major premise domain head
    -- (e.g., List.{0} RCasesPatt → levels = [Level.zero]).
    -- For standard case: map ctor level param i → rec level param (levelOffset + i).
    let recLevelCount := rec.numLevels
    let ctorLevelCount := ctorCi.cv.numLevels
    let levelSubst : Array (Level m) :=
      if cnp > np then
        match majorPremiseDom with
        | some dom => match dom.getAppFn with
          | .const _ lvls _ => lvls
          | _ => #[]
        | none => #[]
      else
        let levelOffset := recLevelCount - ctorLevelCount
        Array.ofFn (n := ctorLevelCount) fun i =>
          .param (levelOffset + i.val) (default : MetaField m Ix.Name)
    let ctorLevels := levelSubst
    -- Extract nested param values from the major premise domain args.
    let nestedParams : Array (Expr m) :=
      if cnp > np then
        match majorPremiseDom with
        | some dom =>
          let args := dom.getAppArgs
          -- args[np..cnp-1] are nested param values (under np+nm+nk+ni binders)
          -- Shift up by nf to account for field binders in rule context
          Array.ofFn (n := cnp - np) fun i =>
            if np + i.val < args.size then
              shiftCtorToRule args[np + i.val]! 0 nf #[]
            else default
        | none => #[]
      else #[]
    -- Peel ALL constructor params (cnp, not just np)
    let mut cty := ctorType
    for _ in [:cnp] do
      match cty with
      | .forallE _ body _ _ => cty := body
      | _ => throw "constructor type has too few Pi binders for params"
    -- cty has nf field Pi binders and cnp free param bvars
    let mut fieldDoms : Array (Expr m) := #[]
    let mut ctorRetType := cty
    for _ in [:nf] do
      match ctorRetType with
      | .forallE dom body _ _ =>
        fieldDoms := fieldDoms.push dom
        ctorRetType := body
      | _ => throw "constructor type has too few Pi binders for fields"
    -- ctorRetType has cnp free param bvars and nf free field bvars.
    -- Extra nested param bvars (0..cnp-np-1 at depth 0, i.e. indices nf..nf+cnp-np-1 in body)
    -- need to be substituted with nestedParams before shifting.
    -- Substitute extra param bvars: in the body, extra params are bvar indices
    -- 0..cnp-np-1 (after fields). We instantiate them and shift shared params down.
    let ctorRet := if cnp > np then
      substNestedParams ctorRetType nf (cnp - np) nestedParams
    else ctorRetType
    let fieldDomsAdj := if cnp > np then
      Array.ofFn (n := fieldDoms.size) fun i =>
        substNestedParams fieldDoms[i]! i.val (cnp - np) nestedParams
    else fieldDoms
    -- Now ctorRet has np free param bvars and nf free field bvars
    -- Shift param bvars (>= nf) up by nm+nk for the rule context
    let ctorRetShifted := shiftCtorToRule ctorRet nf shift levelSubst
    -- 3. Build expected return type: motive indices (ctor params fields)
    -- Under all np+nm+nk+nf binders:
    --   motive_d = bvar (nf + nk + nm - 1 - d)  [d = position of major inductive in rec.all]
    --   param i  = bvar (nf + nk + nm + np - 1 - i)
    --   field k  = bvar (nf - 1 - k)
    let motiveIdx := nf + nk + nm - 1 - motivePos
    let mut ret := Expr.mkBVar motiveIdx
    -- Apply indices from shifted ctor return type (skip all cnp param args)
    let ctorRetArgs := ctorRetShifted.getAppArgs
    for i in [cnp:ctorRetArgs.size] do
      ret := Expr.mkApp ret ctorRetArgs[i]!
    -- Build ctor application: ctor levels params fields nested-params
    let mut ctorApp : Expr m := Expr.mkConst ctorAddr ctorLevels
    for i in [:np] do
      ctorApp := Expr.mkApp ctorApp (Expr.mkBVar (nf + shift + np - 1 - i))
    for v in nestedParams do
      ctorApp := Expr.mkApp ctorApp v
    for k in [:nf] do
      ctorApp := Expr.mkApp ctorApp (Expr.mkBVar (nf - 1 - k))
    ret := Expr.mkApp ret ctorApp
    -- 4. Wrap return type with field Pi binders (innermost first, shifted)
    let mut fullType := ret
    for i in [:nf] do
      let j := nf - 1 - i
      let dom := shiftCtorToRule fieldDomsAdj[j]! j shift levelSubst
      fullType := .forallE dom fullType default default
    -- 5. Wrap with recursor binder Pi's (minors, motives, params - outermost first → innermost first)
    for i in [:np + nm + nk] do
      let j := np + nm + nk - 1 - i
      fullType := .forallE recDoms[j]! fullType default default
    -- 6. Check inferred RHS type matches expected type
    let (_, rhsType) ← withInferOnly (infer ruleRhs)
    if !(← withInferOnly (isDefEq rhsType fullType)) then
      -- Walk both types in parallel, peeling Pi binders, to find where they diverge
      let mut rTy := rhsType
      let mut eTy := fullType
      let mut binderIdx := 0
      let mut divergeMsg := "types differ at top level"
      let mut found := false
      for _ in [:np + nm + nk + nf + 10] do  -- enough iterations
        if found then break
        match rTy, eTy with
        | .forallE rd rb _ _, .forallE ed eb _ _ =>
          if !(← withInferOnly (isDefEq rd ed)) then
            divergeMsg := s!"binder {binderIdx} domain differs"
            found := true
          else
            rTy := rb; eTy := eb; binderIdx := binderIdx + 1
        | _, _ =>
          if !(← withInferOnly (isDefEq rTy eTy)) then
            let rHead := rTy.getAppFn
            let eHead := eTy.getAppFn
            let rArgs := rTy.getAppArgs
            let eArgs := eTy.getAppArgs
            let headEq ← withInferOnly (isDefEq rHead eHead)
            let rTag := if rHead.isBVar then s!"bvar{rHead.bvarIdx!}" else if rHead.isConst then "const" else "other"
            let eTag := if eHead.isBVar then s!"bvar{eHead.bvarIdx!}" else if eHead.isConst then "const" else "other"
            let mut argDiag := s!"rHead={rTag} eHead={eTag} headEq={headEq} rArgs={rArgs.size} eArgs={eArgs.size}"
            if headEq then
              for j in [:min rArgs.size eArgs.size] do
                if !(← withInferOnly (isDefEq rArgs[j]! eArgs[j]!)) then
                  argDiag := argDiag ++ s!" arg{j}differs"
                  break
            divergeMsg := s!"return type differs after {binderIdx} binders; {argDiag}"
            found := true
          else
            divergeMsg := s!"types are actually equal after {binderIdx} binders??"
            found := true
      throw s!"recursor rule RHS type mismatch for constructor {ctorCi.cv.name} ({ctorAddr}): {divergeMsg} (np={np} cnp={cnp})"

  /-- Quick structural equality check without WHNF. Returns:
      - some true: definitely equal
      - some false: definitely not equal
      - none: unknown, need deeper checks -/
  partial def quickIsDefEq (t s : Expr m) (useHash : Bool := true) : TypecheckM m (Option Bool) := do
    -- Run EquivManager structural walk with union-find
    let stt ← get
    let (result, mgr') := EquivManager.isEquiv useHash t s |>.run stt.eqvManager
    modify fun stt => { stt with eqvManager := mgr' }
    if result then return some true
    -- Failure cache (EquivManager only tracks successes)
    let key := eqCacheKey t s
    if (← get).failureCache.contains key then return some false
    -- Shape-specific checks with richer equality (Level.equalLevel, etc.)
    match t, s with
    | .sort u, .sort u' => pure (some (Level.equalLevel u u'))
    | .const a us _, .const b us' _ =>
      if a == b && equalUnivArrays us us' then pure (some true) else pure none
    | .lit l, .lit l' => pure (some (l == l'))
    | .bvar i _, .bvar j _ => if i == j then pure (some true) else pure none
    | .lam .., .lam .. => do
      let mut a := t; let mut b := s
      repeat
        match a, b with
        | .lam ty body _ _, .lam ty' body' _ _ =>
          match ← quickIsDefEq ty ty' with
          | some true => a := body; b := body'
          | other => return other
        | _, _ => break
      quickIsDefEq a b
    | .forallE .., .forallE .. => do
      let mut a := t; let mut b := s
      repeat
        match a, b with
        | .forallE ty body _ _, .forallE ty' body' _ _ =>
          match ← quickIsDefEq ty ty' with
          | some true => a := body; b := body'
          | other => return other
        | _, _ => break
      quickIsDefEq a b
    | _, _ => pure none

  /-- Check if two expressions are definitionally equal.
      Uses a staged approach matching lean4/lean4lean:
      1. quickIsDefEq — structural shape match without WHNF
      2. whnfCore(cheapProj=true) — structural reduction, projections stay cheap
      3. Lazy delta reduction — unfold definitions one step at a time
      4. whnfCore(cheapProj=false) — full projection resolution (only if needed)
      5. Structural comparison -/
  partial def isDefEq (t s : Expr m) : TypecheckM m Bool := do
    -- 0. Quick structural check FIRST — no fuel/stack cost for trivial cases
    match ← quickIsDefEq t s with
    | some result => return result
    | none => pure ()
    modify fun s => { s with isDefEqCalls := s.isDefEqCalls + 1 }
    withRecDepthCheck do
    withFuelCheck do

    -- Bool.true proof-by-reflection (matches lean4 C++ is_def_eq_core)
    -- If one side is Bool.true, fully reduce the other and check
    let prims := (← read).prims
    if s.isConstOf prims.boolTrue then
      let t' ← whnf t
      if t'.isConstOf prims.boolTrue then cacheResult t s true; return true
    if t.isConstOf prims.boolTrue then
      let s' ← whnf s
      if s'.isConstOf prims.boolTrue then cacheResult t s true; return true

    -- 1. Structural reduction (cheapProj=true: defer full projection resolution)
    let tn ← whnfCore t (cheapProj := true)
    let sn ← whnfCore s (cheapProj := true)

    -- 2. Quick check after whnfCore (useHash=false for thorough union-find walking)
    match ← quickIsDefEq tn sn (useHash := false) with
    | some true => cacheResult t s true; return true
    | some false => pure ()  -- don't cache — deeper checks may still succeed
    | none => pure ()

    -- 3. Proof irrelevance
    match ← isDefEqProofIrrel tn sn with
    | some result =>
      cacheResult t s result
      return result
    | none => pure ()

    -- 4. Lazy delta reduction (incremental unfolding)
    let (tn', sn', deltaResult) ← lazyDeltaReduction tn sn
    if let some result := deltaResult then
      cacheResult t s result
      return result

    -- 4b. Cheap structural checks after lazy delta (before full whnfCore)
    match tn', sn' with
    | .const a us _, .const b us' _ =>
      if a == b && equalUnivArrays us us' then
        cacheResult t s true; return true
    | .proj _ ti te _, .proj _ si se _ =>
      if ti == si then
        if ← isDefEq te se then
          cacheResult t s true; return true
    | _, _ => pure ()

    -- 5. Full structural reduction (no cheapProj — resolve all projections)
    let tnn ← whnfCore tn'
    let snn ← whnfCore sn'
    -- If terms changed, recurse (goes through withRecDepthCheck, matching lean4lean)
    if !(tnn == tn' && snn == sn') then
      let result ← isDefEq tnn snn
      cacheResult t s result
      return result
    -- 6. Structural comparison on fully-reduced terms
    let result ← isDefEqCore tnn snn
    cacheResult t s result
    return result

  /-- Check if e lives in Prop: type_of(e) reduces to Sort 0.
      Matches lean4lean's `isProp`. -/
  partial def isProp (e : Expr m) : TypecheckM m Bool := do
    let (_, ty) ← withInferOnly (infer e)
    let ty' ← whnf ty
    return ty' == .sort .zero

  /-- Check if both terms are proofs of the same Prop type (proof irrelevance).
      Returns `none` if inference fails on open terms or the type isn't Prop.
      Guards only the initial infer calls — if types are inferred, isProp and
      isDefEq errors propagate (matching lean4lean's behavior). -/
  partial def isDefEqProofIrrel (t s : Expr m) : TypecheckM m (Option Bool) := do
    let tType ← try let (_, ty) ← withInferOnly (infer t); pure (some ty) catch _ => pure none
    let some tType := tType | return none
    if !(← isProp tType) then return none
    let sType ← try let (_, ty) ← withInferOnly (infer s); pure (some ty) catch _ => pure none
    let some sType := sType | return none
    let result ← isDefEq tType sType
    return some result

  /-- Core structural comparison after whnf. -/
  partial def isDefEqCore (t s : Expr m) : TypecheckM m Bool := do
    match t, s with
    -- Sort
    | .sort u, .sort u' => pure (Level.equalLevel u u')

    -- Bound variable
    | .bvar i _, .bvar j _ => pure (i == j)

    -- Constant
    | .const a us _, .const b us' _ =>
      pure (a == b && equalUnivArrays us us')

    -- Lambda: flatten binder chain to avoid O(num_binders) stack depth
    -- Extend context at each binder so proof irrelevance / infer work on bodies
    | .lam .., .lam .. => do
      let mut a := t
      let mut b := s
      let mut extTypes := (← read).types
      let mut extLetValues := (← read).letValues
      repeat
        match a, b with
        | .lam ty body _ _, .lam ty' body' _ _ =>
          if !(← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isDefEq ty ty')) then return false
          extTypes := extTypes.push ty
          extLetValues := extLetValues.push none
          a := body; b := body'
        | _, _ => break
      withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isDefEq a b)

    -- Pi/ForallE: flatten binder chain to avoid O(num_binders) stack depth
    -- Extend context at each binder so proof irrelevance / infer work on bodies
    | .forallE .., .forallE .. => do
      let mut a := t
      let mut b := s
      let mut extTypes := (← read).types
      let mut extLetValues := (← read).letValues
      repeat
        match a, b with
        | .forallE ty body _ _, .forallE ty' body' _ _ =>
          if !(← withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isDefEq ty ty')) then return false
          extTypes := extTypes.push ty
          extLetValues := extLetValues.push none
          a := body; b := body'
        | _, _ => break
      withReader (fun ctx => { ctx with types := extTypes, letValues := extLetValues }) (isDefEq a b)

    -- Application: flatten app spine, with eta-struct fallback (matches lean4lean)
    | .app .., .app .. => do
      let tFn := t.getAppFn
      let sFn := s.getAppFn
      let tArgs := t.getAppArgs
      let sArgs := s.getAppArgs
      if tArgs.size == sArgs.size then
        if (← isDefEq tFn sFn) then
          let mut ok := true
          for h : i in [:tArgs.size] do
            if !(← isDefEq tArgs[i] sArgs[i]!) then ok := false; break
          if ok then return true
      -- Fallback: try eta-struct when isDefEqApp fails
      tryEtaStruct t s

    -- Projection
    | .proj a i struct _, .proj b j struct' _ =>
      if a == b && i == j then isDefEq struct struct'
      else pure false

    -- Literals
    | .lit l, .lit l' => pure (l == l')

    -- Eta expansion: lambda vs non-lambda
    | .lam ty body _ _, _ => do
      -- eta: (\x => body) =?= s  iff  body =?= s x  where x = bvar 0
      let sLifted := s.liftBVars 1
      let sApp := Expr.mkApp sLifted (Expr.mkBVar 0)
      withExtendedCtx ty (isDefEq body sApp)

    | _, .lam ty body _ _ => do
      -- eta: t =?= (\x => body)  iff  t x =?= body
      let tLifted := t.liftBVars 1
      let tApp := Expr.mkApp tLifted (Expr.mkBVar 0)
      withExtendedCtx ty (isDefEq tApp body)

    -- Nat literal vs non-literal: expand to constructor form but stay in isDefEqCore
    -- (calling full isDefEq would reduce Nat.succ(lit n) back to lit(n+1), causing a cycle)
    | .lit (.natVal _), _ => do
      let prims := (← read).prims
      let expanded := toCtorIfLit prims t
      if expanded == t then pure false
      else isDefEqCore expanded s

    | _, .lit (.natVal _) => do
      let prims := (← read).prims
      let expanded := toCtorIfLit prims s
      if expanded == s then pure false
      else isDefEqCore t expanded

    -- String literal vs constructor expansion
    | .lit (.strVal str), _ => do
      let prims := (← read).prims
      let expanded := strLitToConstructor prims str
      isDefEq expanded s

    | _, .lit (.strVal str) => do
      let prims := (← read).prims
      let expanded := strLitToConstructor prims str
      isDefEq t expanded

    -- Structure eta (one side is app, other is not), with unit-like fallback
    | _, .app _ _ | .app _ _, _ => do
      if ← tryEtaStruct t s then return true
      isDefEqUnitLike t s

    -- Unit-like fallback: non-recursive, single ctor with 0 fields, 0 indices
    | _, _ => isDefEqUnitLike t s

  /-- For unit-like types (non-recursive, single ctor with 0 fields, 0 indices),
      two terms are defeq if their types are defeq. -/
  partial def isDefEqUnitLike (t s : Expr m) : TypecheckM m Bool := do
    let kenv := (← read).kenv
    let (_, tType) ← withInferOnly (infer t)
    let tType' ← whnf tType
    let fn := tType'.getAppFn
    match fn with
    | .const addr _ _ =>
      match kenv.find? addr with
      | some (.inductInfo v) =>
        if v.isRec || v.numIndices != 0 || v.ctors.size != 1 then return false
        match kenv.find? v.ctors[0]! with
        | some (.ctorInfo cv) =>
          if cv.numFields != 0 then return false
          let (_, sType) ← withInferOnly (infer s)
          isDefEq tType sType
        | _ => return false
      | _ => return false
    | _ => return false

  /-- If e is an application whose head is a projection, try whnfCore to reduce it. -/
  partial def tryUnfoldProjApp (e : Expr m) : TypecheckM m (Option (Expr m)) := do
    match e.getAppFn with
    | .proj .. =>
      let e' ← whnfCore e
      if e' == e then return none else return some e'
    | _ => return none

  /-- Check if two Nat.succ chains or zero values match structurally. -/
  partial def isDefEqOffset (t s : Expr m) : TypecheckM m (Option Bool) := do
    let prims := (← read).prims
    let isZero (e : Expr m) := e.isConstOf prims.natZero || match e with | .lit (.natVal 0) => true | _ => false
    let succOf? (e : Expr m) : Option (Expr m) := match e with
      | .lit (.natVal (n+1)) => some (.lit (.natVal n))
      | .app fn arg => if fn.isConstOf prims.natSucc then some arg else none
      | _ => none
    if isZero t && isZero s then return some true
    match succOf? t, succOf? s with
    | some t', some s' => some <$> isDefEq t' s'
    | _, _ => return none

  /-- Lazy delta reduction loop. Unfolds definitions one step at a time,
      guided by ReducibilityHints, until a conclusive comparison or both
      sides are stuck. -/
  partial def lazyDeltaReduction (t s : Expr m)
      : TypecheckM m (Expr m × Expr m × Option Bool) := do
    let mut tn := t
    let mut sn := s
    let kenv := (← read).kenv
    let mut steps := 0
    repeat
      if steps > 10000 then throw "lazyDeltaReduction step limit (10000) exceeded"
      steps := steps + 1

      -- Syntactic check
      if tn == sn then return (tn, sn, some true)

      -- Quick structural check (EquivManager + lambda/forall matching)
      -- Only trust "definitely equal"; delta reduction may still make unequal terms equal
      match ← quickIsDefEq tn sn (useHash := false) with
      | some true => return (tn, sn, some true)
      | _ => pure ()

      -- isDefEqOffset: short-circuit Nat.succ chain comparison
      match ← isDefEqOffset tn sn with
      | some result => return (tn, sn, some result)
      | none => pure ()

      -- Try nat reduction (whnf's args like lean4lean's reduceNat)
      if let some tn' ← tryReduceNat tn then
        return (tn', sn, some (← isDefEq tn' sn))
      if let some sn' ← tryReduceNat sn then
        return (tn, sn', some (← isDefEq tn sn'))

      -- Try native reduction (reduceBool/reduceNat markers)
      let prims := (← read).prims
      if prims.reduceBool != default || prims.reduceNat != default then
        if let some tn' ← reduceNativeExpr tn then
          return (tn', sn, some (← isDefEq tn' sn))
        if let some sn' ← reduceNativeExpr sn then
          return (tn, sn', some (← isDefEq tn sn'))

      -- Lazy delta step
      let tDelta := isDelta tn kenv
      let sDelta := isDelta sn kenv
      match tDelta, sDelta with
      | none, none => return (tn, sn, none)  -- both stuck
      | some dt, none =>
        -- Try reducing projection-headed app on the stuck side first
        if let some sn' ← tryUnfoldProjApp sn then
          sn := sn'; continue
        match unfoldDelta dt tn with
        | some r => tn ← whnfCore r (cheapProj := true); continue
        | none => return (tn, sn, none)
      | none, some ds =>
        -- Try reducing projection-headed app on the stuck side first
        if let some tn' ← tryUnfoldProjApp tn then
          tn := tn'; continue
        match unfoldDelta ds sn with
        | some r => sn ← whnfCore r (cheapProj := true); continue
        | none => return (tn, sn, none)
      | some dt, some ds =>
        let ht := dt.hints
        let hs := ds.hints
        -- Same head optimization: try comparing args first (with failure cache)
        if tn.isApp && sn.isApp && sameHeadConst tn sn && ht.isRegular then
          let key := eqCacheKey tn sn
          if !(← get).failureCache.contains key then
            if equalUnivArrays tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
              if ← isDefEqApp tn sn then return (tn, sn, some true)
            modify fun stt => { stt with failureCache := stt.failureCache.insert key () }
        if ht.lt' hs then
          match unfoldDelta ds sn with
          | some r => sn ← whnfCore r (cheapProj := true); continue
          | none =>
            match unfoldDelta dt tn with
            | some r => tn ← whnfCore r (cheapProj := true); continue
            | none => return (tn, sn, none)
        else if hs.lt' ht then
          match unfoldDelta dt tn with
          | some r => tn ← whnfCore r (cheapProj := true); continue
          | none =>
            match unfoldDelta ds sn with
            | some r => sn ← whnfCore r (cheapProj := true); continue
            | none => return (tn, sn, none)
        else
          -- Same height: unfold both
          match unfoldDelta dt tn, unfoldDelta ds sn with
          | some rt, some rs =>
            tn ← whnfCore rt (cheapProj := true)
            sn ← whnfCore rs (cheapProj := true)
            continue
          | some rt, none => tn ← whnfCore rt (cheapProj := true); continue
          | none, some rs => sn ← whnfCore rs (cheapProj := true); continue
          | none, none => return (tn, sn, none)
    return (tn, sn, none)

  /-- Compare arguments of two applications with the same head constant. -/
  partial def isDefEqApp (t s : Expr m) : TypecheckM m Bool := do
    let tArgs := t.getAppArgs
    let sArgs := s.getAppArgs
    if tArgs.size != sArgs.size then return false
    -- Also compare universe params
    let tFn := t.getAppFn
    let sFn := s.getAppFn
    match tFn, sFn with
    | .const _ us _, .const _ us' _ =>
      if !equalUnivArrays us us' then return false
    | _, _ => pure ()
    for h : i in [:tArgs.size] do
      if !(← isDefEq tArgs[i] sArgs[i]!) then return false
    return true

  /-- Try eta expansion for structure-like types.
      Matches lean4lean's `tryEtaStruct`: constructs projections and compares via `isDefEq`. -/
  partial def tryEtaStruct (t s : Expr m) : TypecheckM m Bool := do
    if ← tryEtaStructCore t s then return true
    tryEtaStructCore s t
  where
    tryEtaStructCore (t s : Expr m) : TypecheckM m Bool := do
      let .const ctorAddr _ _ := s.getAppFn | return false
      match (← read).kenv.find? ctorAddr with
      | some (.ctorInfo cv) =>
        let sArgs := s.getAppArgs
        unless sArgs.size == cv.numParams + cv.numFields do return false
        unless (← read).kenv.isStructureLike cv.induct do return false
        let (_, tType) ← withInferOnly (infer t)
        let (_, sType) ← withInferOnly (infer s)
        unless ← isDefEq tType sType do return false
        for h : i in [:cv.numFields] do
          let argIdx := cv.numParams + i
          let proj := Expr.mkProj cv.induct i t
          unless ← isDefEq proj sArgs[argIdx]! do return false
        return true
      | _ => return false

  /-- Cache a def-eq result (both successes and failures). -/
  partial def cacheResult (t s : Expr m) (result : Bool) : TypecheckM m Unit := do
    if result then
      modify fun stt =>
        let (_, mgr') := EquivManager.addEquiv t s |>.run stt.eqvManager
        { stt with eqvManager := mgr' }
    else
      let key := eqCacheKey t s
      modify fun stt => { stt with failureCache := stt.failureCache.insert key () }

  /-- Validate a primitive definition/inductive/quotient using the KernelOps callback. -/
  partial def validatePrimitive (addr : Address) : TypecheckM m Unit := do
    let ops : KernelOps m := { isDefEq, whnf, infer, isProp, isSort }
    let prims := (← read).prims
    let kenv := (← read).kenv
    let _ ← checkPrimitive ops prims kenv addr

  /-- Validate quotient constant type signatures. -/
  partial def validateQuotient : TypecheckM m Unit := do
    let ops : KernelOps m := { isDefEq, whnf, infer, isProp, isSort }
    let prims := (← read).prims
    checkEqType ops prims
    checkQuotTypes ops prims

end -- mutual

/-! ## Expr size -/

/-- Count the number of nodes in an expression (iterative). -/
partial def Expr.nodeCount (e : Expr m) : Nat := Id.run do
  let mut stack : Array (Expr m) := #[e]
  let mut count : Nat := 0
  while h : stack.size > 0 do
    let cur := stack[stack.size - 1]
    stack := stack.pop
    count := count + 1
    match cur with
    | .app fn arg => stack := stack.push fn |>.push arg
    | .lam ty body _ _ => stack := stack.push ty |>.push body
    | .forallE ty body _ _ => stack := stack.push ty |>.push body
    | .letE ty val body _ => stack := stack.push ty |>.push val |>.push body
    | .proj _ _ s _ => stack := stack.push s
    | _ => pure ()
  return count

/-! ## Top-level entry points -/

/-- Typecheck a single constant by address. -/
def typecheckConst (kenv : Env m) (prims : Primitives) (addr : Address)
    (quotInit : Bool := true) (trace : Bool := false) : Except String Unit :=
  let ctx : TypecheckCtx m := {
    types := #[], kenv := kenv,
    prims := prims, safety := .safe, quotInit := quotInit,
    mutTypes := default, recAddr? := none, trace := trace
  }
  let stt : TypecheckState m := { typedConsts := default }
  let (result, stt') := TypecheckM.run ctx stt (checkConst addr)
  match result with
  | .ok () => .ok ()
  | .error e =>
    .error s!"{e}\n  [stats] maxDepth={stt'.maxRecDepth} fuel={defaultFuel - stt'.fuel} infer={stt'.inferCalls} whnf={stt'.whnfCalls} isDefEq={stt'.isDefEqCalls} inferHits={stt'.inferCacheHits} whnfHits={stt'.whnfCacheHits} whnfCoreHits={stt'.whnfCoreCacheHits}"

/-- Typecheck all constants in a kernel environment. -/
def typecheckAll (kenv : Env m) (prims : Primitives) (quotInit : Bool := true)
    : Except String Unit := do
  for (addr, ci) in kenv do
    match typecheckConst kenv prims addr quotInit with
    | .ok () => pure ()
    | .error e =>
      let header := s!"constant {ci.cv.name} ({ci.kindName}, {addr})"
      let typ := ci.type.pp
      let val := match ci.value? with
        | some v => s!"\n  value: {v.pp}"
        | none => ""
      throw s!"{header}: {e}\n  type: {typ}{val}"

/-- Typecheck all constants with IO progress reporting. -/
def typecheckAllIO (kenv : Env m) (prims : Primitives) (quotInit : Bool := true)
    : IO (Except String Unit) := do
  let mut items : Array (Address × ConstantInfo m) := #[]
  for (addr, ci) in kenv do
    items := items.push (addr, ci)
  let total := items.size
  for h : idx in [:total] do
    let (addr, ci) := items[idx]
    (← IO.getStdout).putStrLn s!"  [{idx + 1}/{total}] {ci.cv.name} ({ci.kindName})"
    (← IO.getStdout).flush
    match typecheckConst kenv prims addr quotInit with
    | .ok () =>
      (← IO.getStdout).putStrLn s!"  ✓ {ci.cv.name}"
      (← IO.getStdout).flush
    | .error e =>
      let header := s!"constant {ci.cv.name} ({ci.kindName}, {addr})"
      let typ := ci.type.pp
      let val := match ci.value? with
        | some v => s!"\n    value: {v.pp}"
        | none => ""
      IO.println s!"type: {typ}"
      IO.println s!"val: {val}"
      return .error s!"{header}: {e}"
  return .ok ()

end Ix.Kernel
