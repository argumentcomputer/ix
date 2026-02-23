/-
  Kernel Infer: Type inference and declaration checking.

  Adapted from Yatima.Typechecker.Infer, parameterized over MetaMode.
-/
import Ix.Kernel.Equal

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

/-- Check strict positivity of a field type w.r.t. a set of inductive addresses.
    Returns true if positive, false if negative occurrence found. -/
partial def checkStrictPositivity (ty : Expr m) (indAddrs : Array Address) : Bool :=
  -- If no inductive is mentioned, we're fine
  if !indAddrs.any (exprMentionsConst ty ·) then true
  else match ty with
  | .forallE domain body _ _ =>
    -- Domain must NOT mention any inductive
    if indAddrs.any (exprMentionsConst domain ·) then false
    -- Continue checking body
    else checkStrictPositivity body indAddrs
  | e =>
    -- Not a forall — must be the inductive at the head
    let fn := e.getAppFn
    match fn with
    | .const addr _ _ => indAddrs.any (· == addr)
    | _ => false

/-- Walk a Pi chain, skip numParams binders, then check positivity of each field.
    Returns an error message or none on success. -/
partial def checkCtorPositivity (ctorType : Expr m) (numParams : Nat) (indAddrs : Array Address)
    : Option String :=
  go ctorType numParams
where
  go (ty : Expr m) (remainingParams : Nat) : Option String :=
    match ty with
    | .forallE _domain body _name _bi =>
      if remainingParams > 0 then
        go body (remainingParams - 1)
      else
        -- This is a field — check positivity of its domain
        let domain := ty.bindingDomain!
        if !checkStrictPositivity domain indAddrs then
          some "inductive occurs in negative position (strict positivity violation)"
        else
          go body 0
    | _ => none

/-- Walk a Pi chain past numParams + numFields binders to get the return type.
    Returns the return type expression (with bvars). -/
def getCtorReturnType (ctorType : Expr m) (numParams numFields : Nat) : Expr m :=
  go ctorType (numParams + numFields)
where
  go (ty : Expr m) (n : Nat) : Expr m :=
    match n, ty with
    | 0, e => e
    | n+1, .forallE _ body _ _ => go body n
    | _, e => e

/-- Extract result universe level from an inductive type expression.
    Walks past all forall binders to find the final Sort. -/
def getIndResultLevel (indType : Expr m) : Option (Level m) :=
  go indType
where
  go : Expr m → Option (Level m)
  | .forallE _ body _ _ => go body
  | .sort lvl => some lvl
  | _ => none

/-- Check if a level is definitively non-zero (always ≥ 1). -/
partial def levelIsNonZero : Level m → Bool
  | .succ _ => true
  | .zero => false
  | .param .. => false  -- could be zero
  | .max a b => levelIsNonZero a || levelIsNonZero b
  | .imax _ b => levelIsNonZero b

/-! ## Type info helpers -/

def lamInfo : TypeInfo m → TypeInfo m
  | .proof => .proof
  | _ => .none

def piInfo (dom img : TypeInfo m) : TypecheckM m σ (TypeInfo m) := match dom, img with
  | .sort lvl, .sort lvl' => pure (.sort (Level.reduceIMax lvl lvl'))
  | _, _ => pure .none

def eqSortInfo (inferType expectType : SusValue m) : TypecheckM m σ Bool := do
  match inferType.info, expectType.info with
  | .sort lvl, .sort lvl' => pure (Level.equalLevel lvl lvl')
  | _, _ => pure true  -- info unavailable; defer to structural equality

def infoFromType (typ : SusValue m) : TypecheckM m σ (TypeInfo m) :=
  match typ.info with
  | .sort (.zero) => pure .proof
  | _ =>
    match typ.get with
    | .app (.const addr _ _) _ _ => do
      match (← read).kenv.find? addr with
      | some (.inductInfo v) =>
        -- Check if it's unit-like: one constructor with zero fields
        if v.ctors.size == 1 then
          match (← read).kenv.find? v.ctors[0]! with
          | some (.ctorInfo cv) =>
            if cv.numFields == 0 then pure .unit else pure .none
          | _ => pure .none
        else pure .none
      | _ => pure .none
    | .sort lvl => pure (.sort lvl)
    | _ => pure .none

/-! ## Inference / Checking -/

mutual
  /-- Check that a term has a given type. -/
  partial def check (term : Expr m) (type : SusValue m) : TypecheckM m σ (TypedExpr m) := do
    if (← read).trace then dbg_trace s!"check: {term.tag}"
    let (te, inferType) ← infer term
    if !(← eqSortInfo inferType type) then
      throw s!"Info mismatch on {term.tag}"
    if !(← equal (← read).lvl type inferType) then
      let lvl := (← read).lvl
      let ppInferred ← tryPpValue lvl inferType.get
      let ppExpected ← tryPpValue lvl type.get
      let dumpInferred := inferType.get.dump
      let dumpExpected := type.get.dump
      throw s!"Type mismatch on {term.tag}\n  inferred: {ppInferred}\n  expected: {ppExpected}\n  inferred dump: {dumpInferred}\n  expected dump: {dumpExpected}\n  inferred info: {inferType.info.pp}\n  expected info: {type.info.pp}"
    pure te

  /-- Infer the type of an expression, returning the typed expression and its type. -/
  partial def infer (term : Expr m) : TypecheckM m σ (TypedExpr m × SusValue m) := withFuelCheck do
    if (← read).trace then dbg_trace s!"infer: {term.tag}"
    match term with
    | .bvar idx bvarName => do
      let ctx ← read
      if idx < ctx.lvl then
        let some type := listGet? ctx.types idx
          | throw s!"var@{idx} out of environment range (size {ctx.types.length})"
        let te : TypedExpr m := ⟨← infoFromType type, .bvar idx bvarName⟩
        pure (te, type)
      else
        -- Mutual reference
        match ctx.mutTypes.get? (idx - ctx.lvl) with
        | some (addr, typeValFn) =>
          if some addr == ctx.recAddr? then
            throw s!"Invalid recursion"
          let univs := ctx.env.univs.toArray
          let type := typeValFn univs
          let name ← lookupName addr
          let te : TypedExpr m := ⟨← infoFromType type, .const addr univs name⟩
          pure (te, type)
        | none =>
          throw s!"var@{idx} out of environment range and does not represent a mutual constant"
    | .sort lvl => do
      let univs := (← read).env.univs.toArray
      let lvl := Level.instBulkReduce univs lvl
      let lvl' := Level.succ lvl
      let typ : SusValue m := .mk (.sort (Level.succ lvl')) (.mk fun _ => .sort lvl')
      let te : TypedExpr m := ⟨.sort lvl', .sort lvl⟩
      pure (te, typ)
    | .app fnc arg => do
      let (fnTe, fncType) ← infer fnc
      match fncType.get with
      | .pi dom img piEnv _ _ => do
        let argTe ← check arg dom
        let ctx ← read
        let stt ← get
        let typ := suspend img { ctx with env := piEnv.extendWith (suspend argTe ctx stt) } stt
        let te : TypedExpr m := ⟨← infoFromType typ, .app fnTe.body argTe.body⟩
        pure (te, typ)
      | v =>
        let ppV ← tryPpValue (← read).lvl v
        throw s!"Expected a pi type, got {ppV}\n  dump: {v.dump}\n  fncType info: {fncType.info.pp}\n  function: {fnc.pp}\n  argument: {arg.pp}"
    | .lam ty body lamName lamBi => do
      let (domTe, _) ← isSort ty
      let ctx ← read
      let stt ← get
      let domVal := suspend domTe ctx stt
      let var := mkSusVar (← infoFromType domVal) ctx.lvl lamName
      let (bodTe, imgVal) ← withExtendedCtx var domVal (infer body)
      let te : TypedExpr m := ⟨lamInfo bodTe.info, .lam domTe.body bodTe.body lamName lamBi⟩
      let imgTE ← quoteTyped (ctx.lvl+1) imgVal.getTyped
      let typ : SusValue m := ⟨← piInfo domVal.info imgVal.info,
        Thunk.mk fun _ => Value.pi domVal imgTE ctx.env lamName lamBi⟩
      pure (te, typ)
    | .forallE ty body piName _ => do
      let (domTe, domLvl) ← isSort ty
      let ctx ← read
      let stt ← get
      let domVal := suspend domTe ctx stt
      let domSusVal := mkSusVar (← infoFromType domVal) ctx.lvl piName
      withExtendedCtx domSusVal domVal do
        let (imgTe, imgLvl) ← isSort body
        let sortLvl := Level.reduceIMax domLvl imgLvl
        let typ : SusValue m := .mk (.sort (Level.succ sortLvl)) (.mk fun _ => .sort sortLvl)
        let te : TypedExpr m := ⟨← infoFromType typ, .forallE domTe.body imgTe.body piName default⟩
        pure (te, typ)
    | .letE ty val body letName => do
      let (tyTe, _) ← isSort ty
      let ctx ← read
      let stt ← get
      let tyVal := suspend tyTe ctx stt
      let valTe ← check val tyVal
      let valVal := suspend valTe ctx stt
      let (bodTe, typ) ← withExtendedCtx valVal tyVal (infer body)
      let te : TypedExpr m := ⟨bodTe.info, .letE tyTe.body valTe.body bodTe.body letName⟩
      pure (te, typ)
    | .lit (.natVal _) => do
      let prims := (← read).prims
      let typ : SusValue m := .mk (.sort (Level.succ .zero)) (.mk fun _ => mkConst prims.nat #[])
      let te : TypedExpr m := ⟨.none, term⟩
      pure (te, typ)
    | .lit (.strVal _) => do
      let prims := (← read).prims
      let typ : SusValue m := .mk (.sort (Level.succ .zero)) (.mk fun _ => mkConst prims.string #[])
      let te : TypedExpr m := ⟨.none, term⟩
      pure (te, typ)
    | .const addr constUnivs _ => do
      ensureTypedConst addr
      let ctx ← read
      let univs := ctx.env.univs.toArray
      let reducedUnivs := constUnivs.toList.map (Level.instBulkReduce univs)
      -- Check const type cache (must also match universe parameters)
      match (← get).constTypeCache.get? addr with
      | some (cachedUnivs, cachedTyp) =>
        if cachedUnivs == reducedUnivs then
          let te : TypedExpr m := ⟨← infoFromType cachedTyp, term⟩
          pure (te, cachedTyp)
        else
          let tconst ← derefTypedConst addr
          let env : ValEnv m := .mk [] reducedUnivs
          let stt ← get
          let typ := suspend tconst.type { ctx with env := env } stt
          modify fun stt => { stt with constTypeCache := stt.constTypeCache.insert addr (reducedUnivs, typ) }
          let te : TypedExpr m := ⟨← infoFromType typ, term⟩
          pure (te, typ)
      | none =>
        let tconst ← derefTypedConst addr
        let env : ValEnv m := .mk [] reducedUnivs
        let stt ← get
        let typ := suspend tconst.type { ctx with env := env } stt
        modify fun stt => { stt with constTypeCache := stt.constTypeCache.insert addr (reducedUnivs, typ) }
        let te : TypedExpr m := ⟨← infoFromType typ, term⟩
        pure (te, typ)
    | .proj typeAddr idx struct _ => do
      let (structTe, structType) ← infer struct
      let (ctorType, univs, params) ← getStructInfo structType.get
      let mut ct ← applyType (← withEnv (.mk [] univs) (eval ctorType)) params.reverse
      for i in [:idx] do
        match ct with
        | .pi dom img piEnv _ _ => do
          let info ← infoFromType dom
          let ctx ← read
          let stt ← get
          let proj := suspend ⟨info, .proj typeAddr i structTe.body default⟩ ctx stt
          ct ← withNewExtendedEnv piEnv proj (eval img)
        | _ => pure ()
      match ct with
      | .pi dom _ _ _ _ =>
        let te : TypedExpr m := ⟨← infoFromType dom, .proj typeAddr idx structTe.body default⟩
        pure (te, dom)
      | _ => throw "Impossible case: structure type does not have enough fields"

  /-- Check if an expression is a Sort, returning the typed expr and the universe level. -/
  partial def isSort (expr : Expr m) : TypecheckM m σ (TypedExpr m × Level m) := do
    let (te, typ) ← infer expr
    match typ.get with
    | .sort u => pure (te, u)
    | v =>
      let ppV ← tryPpValue (← read).lvl v
      throw s!"Expected a sort type, got {ppV}\n  expr: {expr.pp}"

  /-- Get structure info from a value that should be a structure type. -/
  partial def getStructInfo (v : Value m) :
      TypecheckM m σ (TypedExpr m × List (Level m) × List (SusValue m)) := do
    match v with
    | .app (.const indAddr univs _) params _ =>
      match (← read).kenv.find? indAddr with
      | some (.inductInfo v) =>
        if v.ctors.size != 1 || params.length != v.numParams then
          throw s!"Expected a structure type, but {v.name} ({indAddr}) has {v.ctors.size} ctors and {params.length}/{v.numParams} params"
        ensureTypedConst indAddr
        let ctorAddr := v.ctors[0]!
        ensureTypedConst ctorAddr
        match (← get).typedConsts.get? ctorAddr with
        | some (.constructor type _ _) =>
          return (type, univs.toList, params)
        | _ => throw s!"Constructor {ctorAddr} is not in typed consts"
      | some ci => throw s!"Expected a structure type, but {indAddr} is a {ci.kindName}"
      | none => throw s!"Expected a structure type, but {indAddr} not found in env"
    | _ =>
      let ppV ← tryPpValue (← read).lvl v
      throw s!"Expected a structure type, got {ppV}"

  /-- Typecheck a constant. With fresh state per declaration, dependencies get
      provisional entries via `ensureTypedConst` and are assumed well-typed. -/
  partial def checkConst (addr : Address) : TypecheckM m σ Unit := withResetCtx do
    -- Reset fuel and per-constant caches
    modify fun stt => { stt with constTypeCache := {} }
    let ctx ← read
    let _ ← ctx.fuelRef.set defaultFuel
    let _ ← ctx.evalCacheRef.set {}
    let _ ← ctx.equalCacheRef.set {}
    -- Skip if already in typedConsts (provisional entry is fine — dependency assumed well-typed)
    if (← get).typedConsts.get? addr |>.isSome then
      return ()
    let ci ← derefConst addr
    let univs := ci.cv.mkUnivParams
    withEnv (.mk [] univs.toList) do
      let newConst ← match ci with
        | .axiomInfo _ =>
          let (type, _) ← isSort ci.type
          pure (TypedConst.axiom type)
        | .opaqueInfo _ =>
          let (type, _) ← isSort ci.type
          let typeSus := suspend type (← read) (← get)
          let value ← withRecAddr addr (check ci.value?.get! typeSus)
          pure (TypedConst.opaque type value)
        | .thmInfo _ =>
          let (type, lvl) ← isSort ci.type
          if !Level.isZero lvl then
            throw s!"theorem type must be a proposition (Sort 0)"
          let typeSus := suspend type (← read) (← get)
          let value ← withRecAddr addr (check ci.value?.get! typeSus)
          pure (TypedConst.theorem type value)
        | .defnInfo v =>
          let (type, _) ← isSort ci.type
          let ctx ← read
          let stt ← get
          let typeSus := suspend type ctx stt
          let part := v.safety == .partial
          let value ←
            if part then
              let typeSusFn := suspend type { ctx with env := ValEnv.mk ctx.env.exprs ctx.env.univs } stt
              let mutTypes : Std.TreeMap Nat (Address × (Array (Level m) → SusValue m)) compare :=
                (Std.TreeMap.empty).insert 0 (addr, fun _ => typeSusFn)
              withMutTypes mutTypes (withRecAddr addr (check v.value typeSus))
            else withRecAddr addr (check v.value typeSus)
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
          -- Extract the major premise's inductive from the recursor type
          let indAddr := getMajorInduct ci.type v.numParams v.numMotives v.numMinors v.numIndices
            |>.getD default
          -- Ensure the inductive has a provisional entry (assumed well-typed with fresh state per decl)
          ensureTypedConst indAddr
          -- Check recursor type
          let (type, _) ← isSort ci.type
          -- (#3) Validate K-flag instead of trusting the environment
          if v.k then
            validateKFlag v indAddr
          -- (#4) Validate recursor rules
          validateRecursorRules v indAddr
          -- Check recursor rules (type-check RHS)
          let typedRules ← v.rules.mapM fun rule => do
            let (rhs, _) ← infer rule.rhs
            pure (rule.nfields, rhs)
          pure (TypedConst.recursor type v.numParams v.numMotives v.numMinors v.numIndices v.k indAddr typedRules)
      modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr newConst }

  /-- Walk a Pi chain to extract the return sort level (the universe of the result type).
      Assumes the expression ends in `Sort u` after `numBinders` forall binders. -/
  partial def getReturnSort (expr : Expr m) (numBinders : Nat) : TypecheckM m σ (Level m) :=
    match numBinders, expr with
    | 0, .sort u => do
      let univs := (← read).env.univs.toArray
      pure (Level.instBulkReduce univs u)
    | 0, _ => do
      -- Not syntactically a sort; try to infer
      let (_, typ) ← infer expr
      match typ.get with
      | .sort u => pure u
      | _ => throw "inductive return type is not a sort"
    | n+1, .forallE dom body _ _ => do
      let (domTe, _) ← isSort dom
      let ctx ← read
      let stt ← get
      let domVal := suspend domTe ctx stt
      let var := mkSusVar (← infoFromType domVal) ctx.lvl
      withExtendedCtx var domVal (getReturnSort body n)
    | _, _ => throw "inductive type has fewer binders than expected"

  /-- Typecheck a mutual inductive block starting from one of its addresses. -/
  partial def checkIndBlock (addr : Address) : TypecheckM m σ Unit := do
    let ci ← derefConst addr
    -- Find the inductive info
    let indInfo ← match ci with
      | .inductInfo _ => pure ci
      | .ctorInfo v =>
        match (← read).kenv.find? v.induct with
        | some ind@(.inductInfo ..) => pure ind
        | _ => throw "Constructor's inductive not found"
      | _ => throw "Expected an inductive"
    let .inductInfo iv := indInfo | throw "unreachable"
    -- Check if already done
    if (← get).typedConsts.get? addr |>.isSome then return ()
    -- Check the inductive type
    let univs := iv.toConstantVal.mkUnivParams
    let (type, _) ← withEnv (.mk [] univs.toList) (isSort iv.type)
    let isStruct := !iv.isRec && iv.numIndices == 0 && iv.ctors.size == 1 &&
      match (← read).kenv.find? iv.ctors[0]! with
      | some (.ctorInfo cv) => cv.numFields > 0
      | _ => false
    modify fun stt => { stt with typedConsts := stt.typedConsts.insert addr (TypedConst.inductive type isStruct) }

    -- Collect all inductive addresses in this mutual block
    let indAddrs := iv.all

    -- Get the inductive's result universe level
    let indResultLevel := getIndResultLevel iv.type

    -- Check constructors
    for (ctorAddr, cidx) in iv.ctors.toList.zipIdx do
      match (← read).kenv.find? ctorAddr with
      | some (.ctorInfo cv) => do
        let ctorUnivs := cv.toConstantVal.mkUnivParams
        let (ctorType, _) ← withEnv (.mk [] ctorUnivs.toList) (isSort cv.type)
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert ctorAddr (TypedConst.constructor ctorType cidx cv.numFields) }

        -- (#5) Check constructor parameter count matches inductive
        if cv.numParams != iv.numParams then
          throw s!"Constructor {ctorAddr} has {cv.numParams} params but inductive has {iv.numParams}"

        -- (#1) Positivity checking (skip for unsafe inductives)
        if !iv.isUnsafe then
          match checkCtorPositivity cv.type cv.numParams indAddrs with
          | some msg => throw s!"Constructor {ctorAddr}: {msg}"
          | none => pure ()

        -- (#2) Universe constraint checking on constructor fields
        -- Each non-parameter field's sort must be ≤ the inductive's result sort.
        -- We check this by inferring the sort of each field type and comparing levels.
        if !iv.isUnsafe then
          if let some indLvl := indResultLevel then
            let indLvlReduced := Level.instBulkReduce univs indLvl
            checkFieldUniverses cv.type cv.numParams ctorAddr indLvlReduced

        -- (#6) Check indices in ctor return type don't mention the inductive
        if !iv.isUnsafe then
          let retType := getCtorReturnType cv.type cv.numParams cv.numFields
          let args := retType.getAppArgs
          -- Index arguments are those after numParams
          for i in [iv.numParams:args.size] do
            for indAddr in indAddrs do
              if exprMentionsConst args[i]! indAddr then
                throw s!"Constructor {ctorAddr} index argument mentions the inductive (unsound)"

      | _ => throw s!"Constructor {ctorAddr} not found"
    -- Note: recursors are checked individually via checkConst's .recInfo branch,
    -- which calls checkConst on the inductives first then checks rules.

  /-- Check that constructor field types have sorts ≤ the inductive's result sort. -/
  partial def checkFieldUniverses (ctorType : Expr m) (numParams : Nat)
      (ctorAddr : Address) (indLvl : Level m) : TypecheckM m σ Unit :=
    go ctorType numParams
  where
    go (ty : Expr m) (remainingParams : Nat) : TypecheckM m σ Unit :=
      match ty with
      | .forallE dom body piName _ =>
        if remainingParams > 0 then do
          let (domTe, _) ← isSort dom
          let ctx ← read
          let stt ← get
          let domVal := suspend domTe ctx stt
          let var := mkSusVar (← infoFromType domVal) ctx.lvl piName
          withExtendedCtx var domVal (go body (remainingParams - 1))
        else do
          -- This is a field — infer its sort level and check ≤ indLvl
          let (domTe, fieldSortLvl) ← isSort dom
          let fieldReduced := Level.reduce fieldSortLvl
          let indReduced := Level.reduce indLvl
          -- Allow if field ≤ ind, OR if ind is Prop (is_zero allows any field)
          if !Level.leq fieldReduced indReduced 0 && !Level.isZero indReduced then
            throw s!"Constructor {ctorAddr} field type lives in a universe larger than the inductive's universe"
          let ctx ← read
          let stt ← get
          let domVal := suspend domTe ctx stt
          let var := mkSusVar (← infoFromType domVal) ctx.lvl piName
          withExtendedCtx var domVal (go body 0)
      | _ => pure ()

  /-- (#3) Validate K-flag: requires non-mutual, Prop, single ctor, zero fields. -/
  partial def validateKFlag (rec : RecursorVal m) (indAddr : Address) : TypecheckM m σ Unit := do
    -- Must be non-mutual
    if rec.all.size != 1 then
      throw "recursor claims K but inductive is mutual"
    -- Look up the inductive
    match (← read).kenv.find? indAddr with
    | some (.inductInfo iv) =>
      -- Must be in Prop
      match getIndResultLevel iv.type with
      | some lvl =>
        if levelIsNonZero lvl then
          throw s!"recursor claims K but inductive is not in Prop"
      | none => throw "recursor claims K but cannot determine inductive's result sort"
      -- Must have single constructor
      if iv.ctors.size != 1 then
        throw s!"recursor claims K but inductive has {iv.ctors.size} constructors (need 1)"
      -- Constructor must have zero fields
      match (← read).kenv.find? iv.ctors[0]! with
      | some (.ctorInfo cv) =>
        if cv.numFields != 0 then
          throw s!"recursor claims K but constructor has {cv.numFields} fields (need 0)"
      | _ => throw "recursor claims K but constructor not found"
    | _ => throw s!"recursor claims K but {indAddr} is not an inductive"

  /-- (#4) Validate recursor rules: check rule count, ctor membership, field counts. -/
  partial def validateRecursorRules (rec : RecursorVal m) (indAddr : Address) : TypecheckM m σ Unit := do
    -- Collect all constructors from the mutual block
    let mut allCtors : Array Address := #[]
    for iAddr in rec.all do
      match (← read).kenv.find? iAddr with
      | some (.inductInfo iv) =>
        allCtors := allCtors ++ iv.ctors
      | _ => throw s!"recursor references {iAddr} which is not an inductive"
    -- Check rule count
    if rec.rules.size != allCtors.size then
      throw s!"recursor has {rec.rules.size} rules but inductive(s) have {allCtors.size} constructors"
    -- Check each rule
    for h : i in [:rec.rules.size] do
      let rule := rec.rules[i]
      -- Rule's constructor must match expected constructor in order
      if rule.ctor != allCtors[i]! then
        throw s!"recursor rule {i} has constructor {rule.ctor} but expected {allCtors[i]!}"
      -- Look up the constructor and validate nfields
      match (← read).kenv.find? rule.ctor with
      | some (.ctorInfo cv) =>
        if rule.nfields != cv.numFields then
          throw s!"recursor rule for {rule.ctor} has nfields={rule.nfields} but constructor has {cv.numFields} fields"
      | _ => throw s!"recursor rule constructor {rule.ctor} not found"
    -- Validate structural counts against the inductive
    match (← read).kenv.find? indAddr with
    | some (.inductInfo iv) =>
      if rec.numParams != iv.numParams then
        throw s!"recursor numParams={rec.numParams} but inductive has {iv.numParams}"
      if rec.numIndices != iv.numIndices then
        throw s!"recursor numIndices={rec.numIndices} but inductive has {iv.numIndices}"
    | _ => pure ()

end -- mutual

/-! ## Top-level entry points -/

/-- Typecheck a single constant by address. -/
def typecheckConst (kenv : Env m) (prims : Primitives) (addr : Address)
    (quotInit : Bool := true) : Except String Unit :=
  runST fun σ => do
    let fuelRef ← ST.mkRef defaultFuel
    let evalRef ← ST.mkRef ({} : Std.HashMap Address (Array (Level m) × Value m))
    let equalRef ← ST.mkRef ({} : Std.HashMap (USize × USize) Bool)
    let ctx : TypecheckCtx m σ := {
      lvl := 0, env := default, types := [], kenv := kenv,
      prims := prims, safety := .safe, quotInit := quotInit,
      mutTypes := default, recAddr? := none,
      fuelRef := fuelRef, evalCacheRef := evalRef, equalCacheRef := equalRef
    }
    let stt : TypecheckState m := { typedConsts := default }
    TypecheckM.run ctx stt (checkConst addr)

/-- Typecheck all constants in a kernel environment.
    Uses fresh state per declaration — dependencies are assumed well-typed. -/
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

/-- Typecheck all constants with IO progress reporting.
    Uses fresh state per declaration — dependencies are assumed well-typed. -/
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
