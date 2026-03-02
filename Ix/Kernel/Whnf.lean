/-
  Kernel Whnf: Environment-based weak head normal form reduction.

  Works directly on `Expr m` with deferred substitution via closures.
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

open Level (instBulkReduce reduceIMax)

/-! ## Helpers -/

/-- Check if an address is a primitive operation that takes arguments. -/
private def isPrimOp (prims : Primitives) (addr : Address) : Bool :=
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

/-- Try to reduce a Nat primitive applied to literal arguments. Returns the reduced Expr. -/
def tryReduceNat (e : Expr m) : TypecheckM m (Option (Expr m)) := do
  let fn := e.getAppFn
  match fn with
  | .const addr _ _ =>
    let prims := (← read).prims
    if !isPrimOp prims addr then return none
    let args := e.getAppArgs
    -- Nat.succ: 1 arg
    if addr == prims.natSucc then
      if args.size >= 1 then
        match args[0]! with
        | .lit (.natVal n) => return some (.lit (.natVal (n + 1)))
        | _ => return none
      else return none
    -- Binary nat operations: 2 args
    else if args.size >= 2 then
      match args[0]!, args[1]! with
      | .lit (.natVal x), .lit (.natVal y) =>
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

mutual
  /-- Structural WHNF: beta, let-zeta, iota-proj. No delta unfolding.
      Uses an iterative loop to avoid deep stack usage:
      - App spines are collected iteratively (not recursively)
      - Beta/let/iota/proj results loop back instead of tail-calling
      When cheapProj=true, projections are returned as-is (no struct reduction).
      When cheapRec=true, recursor applications are returned as-is (no iota reduction). -/
  partial def whnfCore (e : Expr m) (cheapRec := false) (cheapProj := false)
      : TypecheckM m (Expr m) := do
    -- Cache lookup (only for full structural reduction, not cheap)
    let useCache := !cheapRec && !cheapProj
    if useCache then
      if let some r := (← get).whnfCoreCache.get? e then return r
    let r ← whnfCoreImpl e cheapRec cheapProj
    if useCache then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
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
            tryKReduction e addr args major' params motives indAddr
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

  /-- K-reduction: for Prop inductives with single zero-field constructor. -/
  partial def tryKReduction (e : Expr m) (_addr : Address) (args : Array (Expr m))
      (major : Expr m) (params motives : Nat) (indAddr : Address)
      : TypecheckM m (Expr m) := do
    let ctx ← read
    let prims := ctx.prims
    let kenv := ctx.kenv
    -- Check if major is a constructor
    let majorCtor := toCtorIfLit prims major
    let isCtor := match majorCtor.getAppFn with
      | .const ctorAddr _ _ =>
        match kenv.find? ctorAddr with
        | some (.ctorInfo _) => true
        | _ => false
      | _ => false
    -- Also check if the inductive is in Prop
    let isPropInd := match kenv.find? indAddr with
      | some (.inductInfo v) =>
        let rec getSort : Expr m → Bool
          | .forallE _ body _ _ => getSort body
          | .sort (.zero) => true
          | _ => false
        getSort v.type
      | _ => false
    if isCtor || isPropInd then
      -- K-reduction: return the (only) minor premise
      let minorIdx := params + motives
      if h : minorIdx < args.size then
        return args[minorIdx]
      pure e
    else pure e

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
    -- Skip large nat literals to avoid O(n) overhead
    let skipLargeNat := match major with
      | .lit (.natVal n) => indAddr == prims.nat && n > 256
      | _ => false
    if skipLargeNat then return e
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
        tryStructEta e args indices indAddr rules major motives minors
    | _ =>
      tryStructEta e args indices indAddr rules major motives minors

  /-- Structure eta: expand struct-like major via projections. -/
  partial def tryStructEta (e : Expr m) (args : Array (Expr m))
      (indices : Nat) (indAddr : Address)
      (rules : Array (Nat × TypedExpr m)) (major : Expr m)
      (motives minors : Nat) : TypecheckM m (Expr m) := do
    let kenv := (← read).kenv
    if !kenv.isStructureLike indAddr then return e
    match rules[0]? with
    | some (nfields, rhs) =>
      let recFn := e.getAppFn
      let recLevels := recFn.constLevels!
      let params := args.size - motives - minors - indices - 1
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

  /-- Full WHNF with delta unfolding loop.
      whnfCore handles structural reduction (beta, let, iota, cheap proj).
      This loop adds: nat primitives, stuck projection resolution, delta unfolding.
      Projection chains are flattened to avoid deep recursion:
        proj₁(proj₂(proj₃(struct))) → strip all projs, whnf(struct) ONCE,
        then resolve projections iteratively from inside out.
      Tracks nesting depth: when whnf calls nest too deep (from isDefEq ↔ whnf cycles),
      degrades to whnfCore to prevent native stack overflow. -/
  partial def whnf (e : Expr m) : TypecheckM m (Expr m) := withFuelCheck do
    -- Depth guard: when whnf nesting is too deep, degrade to structural-only
    let depth := (← get).whnfDepth
    if depth > 64 then return ← whnfCore e
    modify fun s => { s with whnfDepth := s.whnfDepth + 1 }
    let r ← whnfImpl e
    modify fun s => { s with whnfDepth := s.whnfDepth - 1 }
    pure r

  partial def whnfImpl (e : Expr m) : TypecheckM m (Expr m) := do
    -- Check cache
    if let some r := (← get).whnfCache.get? e then return r
    let mut t ← whnfCore e
    let mut steps := 0
    repeat
      if steps > 10000 then break  -- safety bound
      -- Try nat primitive reduction
      if let some r := ← tryReduceNat t then
        t ← whnfCore r; steps := steps + 1; continue
      -- Handle stuck projections (including inside app chains).
      -- Flatten nested projection chains to avoid deep whnf→whnf recursion.
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
            current ← whnfCore applied
          | none =>
            -- This projection couldn't be resolved. Reconstruct remaining chain.
            let stuck := if args.isEmpty then
              Expr.mkProj typeAddr idx current
            else
              (Expr.mkProj typeAddr idx current).mkAppN args
            current ← whnfCore stuck
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
        t ← whnfCore r; steps := steps + 1; continue
      break
    modify fun s => { s with whnfCache := s.whnfCache.insert e t }
    pure t

  /-- Unfold a single delta step (definition body). -/
  partial def unfoldDefinition (e : Expr m) : TypecheckM m (Option (Expr m)) := do
    let head := e.getAppFn
    match head with
    | .const addr levels _ => do
      let ci ← derefConst addr
      match ci with
      | .defnInfo v =>
        if v.safety == .partial then return none
        let body := v.value.instantiateLevelParams levels
        let args := e.getAppArgs
        return some (body.mkAppN args)
      | .thmInfo v =>
        let body := v.value.instantiateLevelParams levels
        let args := e.getAppArgs
        return some (body.mkAppN args)
      | _ => return none
    | _ => return none
end

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
    | some ci@(.defnInfo v) =>
      if v.safety == .partial then none else some ci
    | some ci@(.thmInfo _) => some ci
    | _ => none
  | _ => none

end Ix.Kernel
