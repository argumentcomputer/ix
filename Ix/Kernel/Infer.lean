/-
  Kernel Infer: Type inference and declaration checking.

  Environment-based kernel: types are Exprs, uses whnf/isDefEq.
-/
import Ix.Kernel.DefEq

namespace Ix.Kernel

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

/-- Infer TypeInfo from a type expression (after whnf). -/
def infoFromType (typ : Expr m) : TypecheckM m (TypeInfo m) := do
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

/-! ## Inference / Checking -/

mutual
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
    if let some (cachedCtx, cachedType) := (← get).inferCache.get? term then
      -- Ptr equality first, structural BEq fallback
      -- For consts/sorts/lits, context doesn't matter (always closed)
      let contextOk := match term with
        | .const .. | .sort .. | .lit .. => true
        | _ => unsafe ptrAddrUnsafe cachedCtx == ptrAddrUnsafe types || cachedCtx == types
      if contextOk then
        let te : TypedExpr m := ⟨← infoFromType cachedType, term⟩
        return (te, cachedType)
    withRecDepthCheck do
    withFuelCheck do
    -- if (← read).trace then dbg_trace s!"infer: {term.tag}"
    let result ← do match term with
      | .bvar idx bvarName => do
        let ctx ← read
        let depth := ctx.types.size
        if idx < depth then
          modify fun stt => { stt with lookups := stt.lookups.push idx }
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
    -- Cache the inferred type with the binding context
    modify fun stt => { stt with inferCache := stt.inferCache.insert term (types, result.2) }
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
    -- Universe level instantiation for the constant's own level params
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
        pure (TypedConst.definition type value part)
      | .quotInfo v =>
        let (type, _) ← isSort ci.type
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
        if !iv.isUnsafe then
          match ← checkCtorFields cv.type cv.numParams indAddrs with
          | some msg => throw s!"Constructor {ctorAddr}: {msg}"
          | none => pure ()
        if !iv.isUnsafe then
          if let some indLvl := indResultLevel then
            checkFieldUniverses cv.type cv.numParams ctorAddr indLvl
        if !iv.isUnsafe then
          let retType := getCtorReturnType cv.type cv.numParams cv.numFields
          let args := retType.getAppArgs
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
    go (ty : Expr m) (remainingParams : Nat) : TypecheckM m Unit :=
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
    | .bvar i _, .bvar j _ => pure (some (i == j))
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
    withRecDepthCheck do
    withFuelCheck do
    let depth := (← get).recDepth
    -- Temporarily removed for call-site tracing

    -- Loop: steps 1-5 may restart when whnfCore(cheapProj=false) changes terms
    let mut ct := t
    let mut cs := s
    repeat
      -- 1. Stage 1: structural reduction (cheapProj=true: defer full projection resolution)
      let tn ← whnfCore ct (cheapProj := true)
      let sn ← whnfCore cs (cheapProj := true)

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
      if deltaResult == some true then
        cacheResult t s true
        return true

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

      -- 5. Stage 2: full structural reduction (no cheapProj — resolve all projections)
      let tnn ← whnfCore tn'
      let snn ← whnfCore sn'
      -- If terms changed, loop back to step 1 instead of recursing into isDefEq
      if !(tnn == tn' && snn == sn') then
        ct := tnn; cs := snn; continue

      -- 6. Structural comparison on fully-reduced terms
      let result ← isDefEqCore tnn snn
      cacheResult t s result
      return result

    -- unreachable, but needed for type checking
    return false

  /-- Check if e lives in Prop: type_of(e) reduces to Sort 0.
      Matches lean4lean's `isProp`. -/
  partial def isProp (e : Expr m) : TypecheckM m Bool := do
    let (_, ty) ← withInferOnly (infer e)
    let ty' ← whnf ty
    return ty' == .sort .zero

  /-- Check if both terms are proofs of the same Prop type (proof irrelevance).
      Returns `none` if inference fails (e.g., free bound variables) or the type isn't Prop. -/
  partial def isDefEqProofIrrel (t s : Expr m) : TypecheckM m (Option Bool) := do
    let tType ← try let (_, ty) ← withInferOnly (infer t); pure (some ty) catch _ => pure none
    let some tType := tType | return none
    let isPropType ← try isProp tType catch e => do
      if (← get).recDepth > 100 then
        dbg_trace s!"isProp FAILED at depth {(← get).recDepth}: {e}"
      pure false
    if !isPropType then return none
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

    -- Application: flatten app spine to avoid O(num_args) stack depth
    | .app .., .app .. => do
      let tFn := t.getAppFn
      let sFn := s.getAppFn
      let tArgs := t.getAppArgs
      let sArgs := s.getAppArgs
      if tArgs.size != sArgs.size then return false
      if !(← isDefEq tFn sFn) then return false
      for h : i in [:tArgs.size] do
        if !(← isDefEq tArgs[i] sArgs[i]!) then return false
      return true

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

    -- Nat literal vs constructor expansion
    | .lit (.natVal _), _ => do
      let prims := (← read).prims
      let expanded := toCtorIfLit prims t
      if expanded == t then pure false
      else isDefEq expanded s

    | _, .lit (.natVal _) => do
      let prims := (← read).prims
      let expanded := toCtorIfLit prims s
      if expanded == s then pure false
      else isDefEq t expanded

    -- String literal vs constructor expansion
    | .lit (.strVal str), _ => do
      let prims := (← read).prims
      let expanded := strLitToConstructor prims str
      isDefEq expanded s

    | _, .lit (.strVal str) => do
      let prims := (← read).prims
      let expanded := strLitToConstructor prims str
      isDefEq t expanded

    -- Structure eta
    | _, .app _ _ => tryEtaStruct t s
    | .app _ _, _ => tryEtaStruct s t

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
      if steps > 10000 then return (tn, sn, none)
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

      -- Try nat reduction
      if let some r := ← tryReduceNat tn then
        tn ← whnfCore r (cheapProj := true); continue
      if let some r := ← tryReduceNat sn then
        sn ← whnfCore r (cheapProj := true); continue

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

  /-- Try eta expansion for structure-like types. -/
  partial def tryEtaStruct (t s : Expr m) : TypecheckM m Bool := do
    -- s should be a constructor application
    let sFn := s.getAppFn
    match sFn with
    | .const ctorAddr _ _ =>
      match (← read).kenv.find? ctorAddr with
      | some (.ctorInfo cv) =>
        let indAddr := cv.induct
        if !(← read).kenv.isStructureLike indAddr then return false
        let sArgs := s.getAppArgs
        -- Check that each field arg is a projection of t
        let numParams := cv.numParams
        for h : i in [:cv.numFields] do
          let argIdx := numParams + i
          if argIdx < sArgs.size then
            let arg := sArgs[argIdx]!
            match arg with
            | .proj a idx struct _ =>
              if a != indAddr || idx != i then return false
              if !(← isDefEq t struct) then return false
            | _ => return false
          else return false
        return true
      | _ => return false
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
    (quotInit : Bool := true) (trace : Bool := false) : Except String (Array Nat) :=
  let ctx : TypecheckCtx m := {
    types := #[], kenv := kenv,
    prims := prims, safety := .safe, quotInit := quotInit,
    mutTypes := default, recAddr? := none, trace := trace
  }
  let stt : TypecheckState m := { typedConsts := default }
  let (result, stt) := TypecheckM.run ctx stt (checkConst addr)
  result.map fun _ => stt.lookups

/-- Typecheck all constants in a kernel environment. -/
def typecheckAll (kenv : Env m) (prims : Primitives) (quotInit : Bool := true)
    : Except String Unit := do
  let mut allLookups := #[]
  for (addr, ci) in kenv do
    match typecheckConst kenv prims addr quotInit with
    | .ok lookups => allLookups := allLookups ++ lookups
    | .error e =>
      let header := s!"constant {ci.cv.name} ({ci.kindName}, {addr})"
      let typ := ci.type.pp
      let val := match ci.value? with
        | some v => s!"\n  value: {v.pp}"
        | none => ""
      throw s!"{header}: {e}\n  type: {typ}{val}"
  let lookupsCounts : Std.HashMap _ _ := default
  let lookupsCounts := allLookups.foldl (init := lookupsCounts) fun acc n =>
    acc.alter n fun count => match count with
      | some count => some (count + 1)
      | none => some 1
  dbg_trace lookupsCounts.toArray

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
    | .ok _ =>
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
