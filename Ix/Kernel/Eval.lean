/-
  Kernel Eval: Expression evaluation, constant/recursor/quot/nat reduction.

  Adapted from Yatima.Typechecker.Eval, parameterized over MetaMode.
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

open Level (instBulkReduce reduceIMax)

def TypeInfo.update (univs : Array (Level m)) : TypeInfo m → TypeInfo m
  | .sort lvl => .sort (instBulkReduce univs lvl)
  | .unit  => .unit
  | .proof => .proof
  | .none  => .none

/-! ## Helpers (needed by mutual block) -/

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

/-- Try to reduce a primitive operation if all arguments are available. -/
private def tryPrimOp (prims : Primitives) (addr : Address)
    (args : List (SusValue m)) : TypecheckM m (Option (Value m)) := do
  -- Nat.succ: 1 arg
  if addr == prims.natSucc then
    if args.length >= 1 then
      match args.head!.get with
      | .lit (.natVal n) => return some (.lit (.natVal (n + 1)))
      | _ => return none
    else return none
  -- Binary nat operations: 2 args
  else if args.length >= 2 then
    let a := args[0]!.get
    let b := args[1]!.get
    match a, b with
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
        let boolName ← lookupName boolAddr
        return some (mkConst boolAddr #[] boolName)
      else if addr == prims.natBle then
        let boolAddr := if x ≤ y then prims.boolTrue else prims.boolFalse
        let boolName ← lookupName boolAddr
        return some (mkConst boolAddr #[] boolName)
      else if addr == prims.natLand then return some (.lit (.natVal (Nat.land x y)))
      else if addr == prims.natLor then return some (.lit (.natVal (Nat.lor x y)))
      else if addr == prims.natXor then return some (.lit (.natVal (Nat.xor x y)))
      else if addr == prims.natShiftLeft then return some (.lit (.natVal (Nat.shiftLeft x y)))
      else if addr == prims.natShiftRight then return some (.lit (.natVal (Nat.shiftRight x y)))
      else return none
    | _, _ => return none
  else return none

/-- Expand a string literal to its constructor form: String.mk (list-of-chars).
    Each character is represented as Char.ofNat n, and the list uses
    List.cons/List.nil at universe level 0. -/
def strLitToCtorVal (prims : Primitives) (s : String) : TypecheckM m (Value m) := do
  let charMkName ← lookupName prims.charMk
  let charName ← lookupName prims.char
  let listNilName ← lookupName prims.listNil
  let listConsName ← lookupName prims.listCons
  let stringMkName ← lookupName prims.stringMk
  let mkCharOfNat (c : Char) : SusValue m :=
    ⟨.none, .mk fun _ =>
      Value.app (.const prims.charMk #[] charMkName)
        [⟨.none, .mk fun _ => .lit (.natVal c.toNat)⟩] [.none]⟩
  let charType : SusValue m :=
    ⟨.none, .mk fun _ => Value.neu (.const prims.char #[] charName)⟩
  let nilVal : Value m :=
    Value.app (.const prims.listNil #[.zero] listNilName) [charType] [.none]
  let listVal := s.toList.foldr (fun c acc =>
    let tail : SusValue m := ⟨.none, .mk fun _ => acc⟩
    let head := mkCharOfNat c
    Value.app (.const prims.listCons #[.zero] listConsName)
      [tail, head, charType] [.none, .none, .none]
  ) nilVal
  let data : SusValue m := ⟨.none, .mk fun _ => listVal⟩
  pure (Value.app (.const prims.stringMk #[] stringMkName) [data] [.none])

/-! ## Eval / Apply mutual block -/

mutual
  /-- Evaluate a typed expression to a value. -/
  partial def eval (t : TypedExpr m) : TypecheckM m (Value m) := withFuelCheck do
    if (← read).trace then dbg_trace s!"eval: {t.body.tag}"
    match t.body with
    | .app fnc arg => do
      let ctx ← read
      let stt ← get
      let argThunk := suspend ⟨default, arg⟩ ctx stt
      let fnc ← evalTyped ⟨default, fnc⟩
      try apply fnc argThunk
      catch e =>
        throw s!"{e}\n  in app: ({fnc.body.summary}) applied to ({arg.pp})"
    | .lam ty body name bi => do
      let ctx ← read
      let stt ← get
      let dom := suspend ⟨default, ty⟩ ctx stt
      pure (.lam dom ⟨default, body⟩ ctx.env name bi)
    | .bvar idx _ => do
      let some thunk := listGet? (← read).env.exprs idx
        | throw s!"Index {idx} is out of range for expression environment"
      pure thunk.get
    | .const addr levels name => do
      let env := (← read).env
      let levels := levels.map (instBulkReduce env.univs.toArray)
      try evalConst addr levels name
      catch e =>
        let nameStr := match (← read).kenv.find? addr with
          | some c => s!"{c.cv.name}" | none => s!"{addr}"
        throw s!"{e}\n  in eval const {nameStr}"
    | .letE _ val body _ => do
      let ctx ← read
      let stt ← get
      let thunk := suspend ⟨default, val⟩ ctx stt
      withExtendedEnv thunk (eval ⟨default, body⟩)
    | .forallE ty body name bi => do
      let ctx ← read
      let stt ← get
      let dom := suspend ⟨default, ty⟩ ctx stt
      pure (.pi dom ⟨default, body⟩ ctx.env name bi)
    | .sort univ => do
      let env := (← read).env
      pure (.sort (instBulkReduce env.univs.toArray univ))
    | .lit lit =>
      pure (.lit lit)
    | .proj typeAddr idx struct typeName => do
      let raw ← eval ⟨default, struct⟩
      -- Expand string literals to constructor form before projecting
      let val ← match raw with
        | .lit (.strVal s) => strLitToCtorVal (← read).prims s
        | v => pure v
      match val with
      | .app (.const ctorAddr _ _) args _ =>
        let ctx ← read
        match ctx.kenv.find? ctorAddr with
        | some (.ctorInfo v) =>
          let idx := v.numParams + idx
          let some arg := listGet? args.reverse idx
            | throw s!"Invalid projection of index {idx} but constructor has only {args.length} arguments"
          pure arg.get
        | _ => do
          let ti := TypeInfo.update (← read).env.univs.toArray (default : TypeInfo m)
          pure (.app (.proj typeAddr idx ⟨ti, val⟩ typeName) [] [])
      | .app _ _ _ => do
        let ti := TypeInfo.update (← read).env.univs.toArray (default : TypeInfo m)
        pure (.app (.proj typeAddr idx ⟨ti, val⟩ typeName) [] [])
      | e => throw s!"Value is impossible to project: {e.ctorName}"

  partial def evalTyped (t : TypedExpr m) : TypecheckM m (AddInfo (TypeInfo m) (Value m)) := do
    let reducedInfo := t.info.update (← read).env.univs.toArray
    let value ← eval t
    pure ⟨reducedInfo, value⟩

  /-- Evaluate a constant that is not a primitive.
      Theorems are treated as opaque (not unfolded) — proof irrelevance handles
      equality of proof terms, and this avoids deep recursion through proof bodies.
      Caches evaluated definition bodies to avoid redundant evaluation. -/
  partial def evalConst' (addr : Address) (univs : Array (Level m)) (name : MetaField m Ix.Name := default) : TypecheckM m (Value m) := do
    match (← read).kenv.find? addr with
    | some (.defnInfo _) =>
      -- Check eval cache (must also match universe parameters)
      if let some (cachedUnivs, cachedVal) := (← get).evalCache.get? addr then
        if cachedUnivs == univs then return cachedVal
      ensureTypedConst addr
      match (← get).typedConsts.get? addr with
      | some (.definition _ deref part) =>
        if part then pure (mkConst addr univs name)
        else
          let val ← withEnv (.mk [] univs.toList) (eval deref)
          modify fun stt => { stt with evalCache := stt.evalCache.insert addr (univs, val) }
          pure val
      | _ => throw "Invalid const kind for evaluation"
    | _ => pure (mkConst addr univs name)

  /-- Evaluate a constant: check if it's Nat.zero, a primitive op, or unfold it. -/
  partial def evalConst (addr : Address) (univs : Array (Level m)) (name : MetaField m Ix.Name := default) : TypecheckM m (Value m) := do
    let prims := (← read).prims
    if addr == prims.natZero then pure (.lit (.natVal 0))
    else if isPrimOp prims addr then pure (mkConst addr univs name)
    else evalConst' addr univs name

  /-- Create a suspended value from a typed expression, capturing context. -/
  partial def suspend (expr : TypedExpr m) (ctx : TypecheckCtx m) (stt : TypecheckState m) : SusValue m :=
    let thunk : Thunk (Value m) := .mk fun _ =>
      match TypecheckM.run ctx stt (eval expr) with
      | .ok a => a
      | .error e => .exception e
    let reducedInfo := expr.info.update ctx.env.univs.toArray
    ⟨reducedInfo, thunk⟩

  /-- Apply a value to an argument. -/
  partial def apply (val : AddInfo (TypeInfo m) (Value m)) (arg : SusValue m) : TypecheckM m (Value m) := do
    if (← read).trace then dbg_trace s!"apply: {val.body.ctorName}"
    match val.body with
    | .lam _ bod lamEnv _ _ =>
      withNewExtendedEnv lamEnv arg (eval bod)
    | .pi dom img piEnv _ _ =>
      -- Propagate TypeInfo: if domain is Prop, argument is a proof
      let enrichedArg : SusValue m := match arg.info, dom.info with
        | .none, .sort (.zero) => ⟨.proof, arg.body⟩
        | _, _ => arg
      withNewExtendedEnv piEnv enrichedArg (eval img)
    | .app (.const addr univs name) args infos => applyConst addr univs arg args val.info infos name
    | .app neu args infos => pure (.app neu (arg :: args) (val.info :: infos))
    | v =>
      throw s!"Invalid case for apply: got {v.ctorName} ({v.summary})"

  /-- Apply a named constant to arguments, handling recursors, quotients, and primitives. -/
  partial def applyConst (addr : Address) (univs : Array (Level m)) (arg : SusValue m)
      (args : List (SusValue m)) (info : TypeInfo m) (infos : List (TypeInfo m))
      (name : MetaField m Ix.Name := default) : TypecheckM m (Value m) := do
    let prims := (← read).prims
    -- Try primitive operations
    if let some result ← tryPrimOp prims addr (arg :: args) then
      return result

    ---- Try recursor/quotient (ensure provisional entry exists for eval-time lookups)
    ensureTypedConst addr
    match (← get).typedConsts.get? addr with
    | some (.recursor _ params motives minors indices isK indAddr rules) =>
      let majorIdx := params + motives + minors + indices
      if args.length != majorIdx then
        pure (.app (.const addr univs name) (arg :: args) (info :: infos))
      else if isK then
        -- K-reduce when major is a constructor, or shortcut via proof irrelevance
        let isKCtor ← match ← toCtorIfLit prims (arg.get) with
          | .app (.const ctorAddr _ _) _ _ =>
            match (← get).typedConsts.get? ctorAddr with
            | some (.constructor ..) => pure true
            | _ => match (← read).kenv.find? ctorAddr with
              | some (.ctorInfo _) => pure true
              | _ => pure false
          | _ => pure false
        -- Also check if the inductive lives in Prop, since eval doesn't track TypeInfo
        let isPropInd := match (← read).kenv.find? indAddr with
          | some (.inductInfo v) =>
            let rec getSort : Expr m → Bool
              | .forallE _ body _ _ => getSort body
              | .sort (.zero) => true
              | _ => false
            getSort v.type
          | _ => false
        if isKCtor || isPropInd || (match arg.info with | .proof => true | _ => false) then
          let nArgs := args.length
          let nDrop := params + motives + 1
          if nArgs < nDrop then throw s!"Too few arguments ({nArgs}). At least {nDrop} needed"
          let minorIdx := nArgs - nDrop
          let some minor := listGet? args minorIdx | throw s!"Index {minorIdx} is out of range"
          pure minor.get
        else
          pure (.app (.const addr univs name) (arg :: args) (info :: infos))
      else
        -- Skip Nat.rec reduction on large literals to avoid O(n) eval overhead
        let skipLargeNat := match arg.get with
          | .lit (.natVal n) => indAddr == prims.nat && n > 256
          | _ => false
        if skipLargeNat then
          pure (.app (.const addr univs name) (arg :: args) (info :: infos))
        else
        match ← toCtorIfLit prims (arg.get) with
        | .app (.const ctorAddr _ _) ctorArgs _ =>
          let st ← get
          let ctx ← read
          let ctorInfo? := match st.typedConsts.get? ctorAddr with
            | some (.constructor _ ctorIdx numFields) => some (ctorIdx, numFields)
            | _ => match ctx.kenv.find? ctorAddr with
              | some (.ctorInfo cv) => some (cv.cidx, cv.numFields)
              | _ => none
          match ctorInfo? with
          | some (ctorIdx, _) =>
            match rules[ctorIdx]? with
            | some (fields, rhs) =>
              let exprs := (ctorArgs.take fields) ++ (args.drop indices)
              withEnv (.mk exprs univs.toList) (eval rhs.toImplicitLambda)
            | none => throw s!"Constructor has no associated recursion rule"
          | none => pure (.app (.const addr univs name) (arg :: args) (info :: infos))
        | _ =>
          -- Structure eta: expand struct-like major via projections
          let kenv := (← read).kenv
          let doStructEta := match arg.info with
            | .proof => false
            | _ => kenv.isStructureLike indAddr
          if doStructEta then
            match rules[0]? with
            | some (fields, rhs) =>
              let mut projArgs : List (SusValue m) := []
              for i in [:fields] do
                let proj : SusValue m := ⟨.none, .mk fun _ =>
                  Value.app (.proj indAddr i ⟨.none, arg.get⟩ default) [] []⟩
                projArgs := proj :: projArgs
              let exprs := projArgs ++ (args.drop indices)
              withEnv (.mk exprs univs.toList) (eval rhs.toImplicitLambda)
            | none => pure (.app (.const addr univs name) (arg :: args) (info :: infos))
          else
            pure (.app (.const addr univs name) (arg :: args) (info :: infos))
    | some (.quotient _ kind) => match kind with
      | .lift => applyQuot prims arg args 6 1 (.app (.const addr univs name) (arg :: args) (info :: infos))
      | .ind  => applyQuot prims arg args 5 0 (.app (.const addr univs name) (arg :: args) (info :: infos))
      | _ => pure (.app (.const addr univs name) (arg :: args) (info :: infos))
    | _ => pure (.app (.const addr univs name) (arg :: args) (info :: infos))

  /-- Apply a quotient to a value. -/
  partial def applyQuot (_prims : Primitives) (major : SusValue m) (args : List (SusValue m))
      (reduceSize argPos : Nat) (default : Value m) : TypecheckM m (Value m) :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major.get with
      | .app (.const majorFn _ _) majorArgs _ => do
        match (← get).typedConsts.get? majorFn with
        | some (.quotient _ .ctor) =>
          if majorArgs.length != 3 then throw "majorArgs should have size 3"
          let some majorArg := majorArgs.head? | throw "majorArgs can't be empty"
          let some head := listGet? args argPos | throw s!"{argPos} is an invalid index for args"
          apply head.getTyped majorArg
        | _ => pure default
      | _ => pure default
    else if argsLength < reduceSize then pure default
    else throw s!"argsLength {argsLength} can't be greater than reduceSize {reduceSize}"

  /-- Convert a nat literal to Nat.succ/Nat.zero constructors. -/
  partial def toCtorIfLit (prims : Primitives) : Value m → TypecheckM m (Value m)
    | .lit (.natVal 0) => do
      let name ← lookupName prims.natZero
      pure (Value.neu (.const prims.natZero #[] name))
    | .lit (.natVal (n+1)) => do
      let name ← lookupName prims.natSucc
      let thunk : SusValue m := ⟨.none, Thunk.mk fun _ => .lit (.natVal n)⟩
      pure (.app (.const prims.natSucc #[] name) [thunk] [.none])
    | v => pure v
end

/-! ## Quoting (read-back from Value to Expr) -/

mutual
  partial def quote (lvl : Nat) : Value m → TypecheckM m (Expr m)
    | .sort univ => do
      let env := (← read).env
      pure (.sort (instBulkReduce env.univs.toArray univ))
    | .app neu args infos => do
      let argsInfos := args.zip infos
      argsInfos.foldrM (init := ← quoteNeutral lvl neu) fun (arg, _info) acc => do
        let argExpr ← quoteTyped lvl arg.getTyped
        pure (.app acc argExpr.body)
    | .lam dom bod env name bi => do
      let dom ← quoteTyped lvl dom.getTyped
      let var := mkSusVar (default : TypeInfo m) lvl name
      let bod ← quoteTypedExpr (lvl+1) bod (env.extendWith var)
      pure (.lam dom.body bod.body name bi)
    | .pi dom img env name bi => do
      let dom ← quoteTyped lvl dom.getTyped
      let var := mkSusVar (default : TypeInfo m) lvl name
      let img ← quoteTypedExpr (lvl+1) img (env.extendWith var)
      pure (.forallE dom.body img.body name bi)
    | .lit lit => pure (.lit lit)
    | .exception e => throw e

  partial def quoteTyped (lvl : Nat) (val : AddInfo (TypeInfo m) (Value m)) : TypecheckM m (TypedExpr m) := do
    pure ⟨val.info, ← quote lvl val.body⟩

  partial def quoteTypedExpr (lvl : Nat) (t : TypedExpr m) (env : ValEnv m) : TypecheckM m (TypedExpr m) := do
    let e ← quoteExpr lvl t.body env
    pure ⟨t.info, e⟩

  partial def quoteExpr (lvl : Nat) (expr : Expr m) (env : ValEnv m) : TypecheckM m (Expr m) :=
    match expr with
    | .bvar idx _ => do
      match listGet? env.exprs idx with
      | some val => quote lvl val.get
      | none => throw s!"Unbound variable _@{idx}"
    | .app fnc arg => do
      let fnc ← quoteExpr lvl fnc env
      let arg ← quoteExpr lvl arg env
      pure (.app fnc arg)
    | .lam ty body n bi => do
      let ty ← quoteExpr lvl ty env
      let var := mkSusVar (default : TypeInfo m) lvl n
      let body ← quoteExpr (lvl+1) body (env.extendWith var)
      pure (.lam ty body n bi)
    | .forallE ty body n bi => do
      let ty ← quoteExpr lvl ty env
      let var := mkSusVar (default : TypeInfo m) lvl n
      let body ← quoteExpr (lvl+1) body (env.extendWith var)
      pure (.forallE ty body n bi)
    | .letE ty val body n => do
      let ty ← quoteExpr lvl ty env
      let val ← quoteExpr lvl val env
      let var := mkSusVar (default : TypeInfo m) lvl n
      let body ← quoteExpr (lvl+1) body (env.extendWith var)
      pure (.letE ty val body n)
    | .const addr levels name =>
      pure (.const addr (levels.map (instBulkReduce env.univs.toArray)) name)
    | .sort univ =>
      pure (.sort (instBulkReduce env.univs.toArray univ))
    | .proj typeAddr idx struct name => do
      let struct ← quoteExpr lvl struct env
      pure (.proj typeAddr idx struct name)
    | .lit .. => pure expr

  partial def quoteNeutral (lvl : Nat) : Neutral m → TypecheckM m (Expr m)
    | .fvar idx name => do
      pure (.bvar (lvl - idx - 1) name)
    | .const addr univs name => do
      let env := (← read).env
      pure (.const addr (univs.map (instBulkReduce env.univs.toArray)) name)
    | .proj typeAddr idx val name => do
      let te ← quoteTyped lvl val
      pure (.proj typeAddr idx te.body name)
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
      -- args = [type, head, tail]
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
    -- Try folding the fully-reconstructed app
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

/-! ## Value pretty printing -/

/-- Pretty-print a value by quoting it back to an Expr, then using Expr.pp.
    Folds Nat/String constructor chains back to literals for readability. -/
partial def ppValue (lvl : Nat) (v : Value m) : TypecheckM m String := do
  let expr ← quote lvl v
  let expr := foldLiterals (← read).prims expr
  return expr.pp

/-- Pretty-print a suspended value. -/
partial def ppSusValue (lvl : Nat) (sv : SusValue m) : TypecheckM m String :=
  ppValue lvl sv.get

/-- Pretty-print a value, falling back to the shallow summary on error. -/
partial def tryPpValue (lvl : Nat) (v : Value m) : TypecheckM m String := do
  try ppValue lvl v
  catch _ => return v.summary

/-- Apply a value to a list of arguments. -/
def applyType (v : Value m) (args : List (SusValue m)) : TypecheckM m (Value m) :=
  match args with
  | [] => pure v
  | arg :: rest => do
    let info : TypeInfo m := .none
    let v' ← try apply ⟨info, v⟩ arg
      catch e =>
        let ppV ← tryPpValue (← read).lvl v
        throw s!"{e}\n  in applyType: {ppV} with {args.length} remaining args"
    applyType v' rest

end Ix.Kernel
