import Ix.Aiur.Term
import Std.Data.HashSet

namespace Aiur

inductive CheckError
  | duplicatedDefinition : Global → CheckError
  | undefinedGlobal : Global → CheckError
  | unboundVariable : Global → CheckError
  | notAConstructor : Global → CheckError
  | notAValue : Global → CheckError
  | notAFunction : Global → CheckError
  | cannotApply : Global → CheckError
  | notADataType : Global → CheckError
  | typeMismatch : Typ → Typ → CheckError
  | illegalReturn : CheckError
  | wrongNumArgs : Global → Nat → Nat → CheckError
  | notATuple : Typ → CheckError
  | notAnArray : Typ → CheckError
  | emptyArray : CheckError
  | indexOoB : Nat → CheckError
  | negativeRange : Nat → Nat → CheckError
  | rangeOoB : Nat → Nat → CheckError
  | incompatiblePattern : Pattern → Typ → CheckError
  | differentBindings : List (Local × Typ) → List (Local × Typ) → CheckError
  | emptyMatch
  | branchMismatch : Typ → Typ → CheckError
  | notAPointer : Typ → CheckError
  | duplicatedBind : Pattern → CheckError
  deriving Repr

instance : ToString CheckError where
  toString e := repr e |>.pretty

/--
Constructs a map of declarations from a toplevel, ensuring that there are no duplicate names
for functions and datatypes.
-/
def Toplevel.mkDecls (toplevel : Toplevel) : Except CheckError Decls := do
  let map ← toplevel.functions.foldlM (init := default)
    fun acc function => addDecl acc Function.name .function function
  toplevel.dataTypes.foldlM (init := map) addDataType
where
  ensureUnique name (map : IndexMap Global _) := do
    if map.containsKey name then throw $ .duplicatedDefinition name
  addDecl {α : Type} map (nameFn : α → Global) (wrapper : α → Declaration) (inner : α) := do
    ensureUnique (nameFn inner) map
    pure $ map.insert (nameFn inner) (wrapper inner)
  addDataType map dataType := do
    let dataTypeName := dataType.name
    ensureUnique dataTypeName map
    let map' := map.insert dataTypeName (.dataType dataType)
    dataType.constructors.foldlM (init := map') fun acc (constructor : Constructor) =>
      addDecl acc (dataTypeName.pushNamespace ∘ Constructor.nameHead) (.constructor dataType) constructor

structure CheckContext where
  decls : Decls
  varTypes : Std.HashMap Local Typ
  returnType : Typ
  unconstrained : Bool

abbrev CheckM := ReaderT CheckContext (Except CheckError)

/-- Retrieves the type of a global reference. -/
def refLookup (global : Global) : CheckM Typ := do
  let ctx ← read
  match ctx.decls.getByKey global with
  | some (.function function) =>
    pure $ .function (function.inputs.map Prod.snd) function.output
  | some (.constructor dataType constructor) =>
    let args := constructor.argTypes
    unless args.isEmpty do (throw $ .wrongNumArgs global args.length 0)
    pure $ .dataType $ dataType.name
  | some _ => throw $ .notAValue global
  | none => throw $ .unboundVariable global

/-- Extend context with locally bound variables. -/
def bindIdents (bindings : List (Local × Typ)) (ctx : CheckContext) : CheckContext :=
  { ctx with varTypes := ctx.varTypes.insertMany bindings }

mutual
partial def inferTerm : Term → CheckM TypedTerm
  | .unit => pure ⟨.unit, .unit, false⟩
  | .var x => do
    -- Retrieves and returns the variable type from the context.
    let ctx ← read
    match ctx.varTypes[x]? with
    | some t => pure ⟨t, .var x, false⟩
    | none =>
      let Local.str localName := x | unreachable!
      let typ ← refLookup (Global.init localName)
      pure ⟨typ, .var x, false⟩
  | .ref x => do
    let typ ← refLookup x
    pure ⟨typ, .ref x, false⟩
  | .ret term => do
    -- Ensures that the type of the returned term matches the expected return type.
    -- The term is not allowed to have a (nested) return.
    -- Returning the type of the term is not necessary because it's already in the context.
    let ctx ← read
    let inner ← checkNoEscape term ctx.returnType
    pure ⟨ctx.returnType, inner, true⟩
  | .data data => do
    let (typ, inner) ← inferData data
    pure ⟨typ, inner, false⟩
  | .let pat expr body => do
    -- Returns the type of the body, inferred in the context extended with the bound variable type.
    -- The bound variable is ensured not to escape.
    let (exprTyp, exprInner) ← inferNoEscape expr
    let expr' := ⟨exprTyp, exprInner, false⟩
    let bindings ← checkPattern pat exprTyp
    let body' ← withReader (bindIdents bindings) (inferTerm body)
    pure ⟨body'.typ, .let pat expr' body', body'.escapes⟩
  | .match term branches => inferMatch term branches
  | .app func@(⟨.str .anonymous unqualifiedFunc⟩) args => do
    -- Ensures the function exists in the context and that the arguments, which aren't allowed to
    -- escape, match the function's input types. Returns the function's output type.
    let ctx ← read
    match ctx.varTypes[Local.str unqualifiedFunc]? with
    | some (.function inputs output) => do
      let args ← checkArgsAndInputs func args inputs
      pure ⟨output, .app func args, false⟩
    | some _ => throw $ .notAFunction func
    | none => match ctx.decls.getByKey func with
      | some (.function function) => do
        let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
        pure ⟨function.output, .app func args, false⟩
      | some (.constructor dataType constr) => do
        let args ← checkArgsAndInputs func args constr.argTypes
        pure ⟨.dataType dataType.name, .app func args, false⟩
      | _ => throw $ .cannotApply func
  | .app func args => do
    -- Only checks global map if it is not unqualified
    let ctx ← read
    match ctx.decls.getByKey func with
    | some (.function function) =>
      let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
      pure ⟨function.output, .app func args, false⟩
    | some (.constructor dataType constr) =>
      let args ← checkArgsAndInputs func args constr.argTypes
      pure ⟨.dataType dataType.name, .app func args, false⟩
    | _ => throw $ .cannotApply func
  | .add a b => do
    let (a, b) ← checkArith a b
    pure ⟨.field, .add a b, false⟩
  | .sub a b => do
    let (a, b) ← checkArith a b
    pure ⟨.field, .sub a b, false⟩
  | .mul a b => do
    let (a, b) ← checkArith a b
    pure ⟨.field, .mul a b, false⟩
  | .eqZero a => do
    let a ← fieldTerm <$> checkNoEscape a .field
    pure ⟨.field, .eqZero a, false⟩
  | .proj tup i => do
    let (typs, tupInner) ← inferTuple tup
    if h : i < typs.size then
      let typ := typs[i]
      let tup := ⟨.tuple typs, tupInner, false⟩
      pure ⟨typ, .proj tup i, false⟩
    else
      throw $ .indexOoB i
  | .get arr i => do
    let (typ, n, inner) ← inferArray arr
    if i ≥ n then
      throw $ .indexOoB i
    else
      let arr := ⟨.array typ n, inner, false⟩
      pure ⟨typ, .get arr i, false⟩
  | .slice arr i j => if j < i then throw $ .negativeRange i j else do
    let (typ, n, inner) ← inferArray arr
    if j ≤ n then
      let arr := ⟨.array typ n, inner, false⟩
      pure ⟨.array typ (j - i), .slice arr i j, false⟩
    else
      throw $ .rangeOoB i j
  | .set arr i val => do
    let (typ, n, inner) ← inferArray arr
    if i ≥ n then
      throw $ .indexOoB i
    else
      let val ← checkNoEscape val typ
      let arrTyp := .array typ n
      let arr := ⟨arrTyp, inner, false⟩
      let val := ⟨typ, val, false⟩
      pure ⟨arrTyp, .set arr i val, false⟩
  | .store term => do
    -- Infers the type of the term and returns it, wrapped by a pointer type.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    let store := .store ⟨typ, inner, false⟩
    pure ⟨.pointer typ, store, false⟩
  | .load term => do
    -- Ensures that the the type of the term is a pointer type and returns the unwrapped type.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    match typ with
    | .pointer innerTyp =>
      let load := .load ⟨typ, inner, false⟩
      pure ⟨innerTyp, load, false⟩
    | _ => throw $ .notAPointer typ
  | .ptrVal term => do
    -- Infers the type of the term, which must be a pointer, but returns `.u64`, as in a cast.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    match typ with
    | .pointer _ => pure $ fieldTerm (.ptrVal ⟨typ, inner, false⟩)
    | _ => throw $ .notAPointer typ
  | .ann typ term => do
    let inner ← checkNoEscape term typ
    pure ⟨typ, inner, false⟩
  -- | .unsafeCast term castTyp => do
  --   let (typ, inner) ← inferNoEscape term
  --   pure ⟨typ, .unsafeCast inner castTyp, false⟩
  | .assertEq a b ret => do
    -- `a` and `b` must have the same type.
    let (typ, a) ← inferNoEscape a
    let b ← checkNoEscape b typ
    let ret ← inferTerm ret
    let assertEq := .assertEq ⟨typ, a, false⟩ ⟨typ, b, false⟩ ret
    assert! (ret.escapes == false)
    pure ⟨ret.typ, assertEq, false⟩
  | .ioGetInfo key => do
    let (typ, keyInner) ← inferNoEscape key
    match typ with
    | .array .. =>
      let ioGetInfo := .ioGetInfo ⟨typ, keyInner, false⟩
      pure ⟨.tuple #[.field, .field], ioGetInfo, false⟩
    | _ => throw $ .notAnArray typ
  | .ioSetInfo key idx len ret => do
    let (keyTyp, keyInner) ← inferNoEscape key
    match keyTyp with
    | .array keyEltTyp _ =>
      if keyEltTyp != .field then throw $ .typeMismatch .field keyEltTyp
      let idx ← fieldTerm <$> checkNoEscape idx .field
      let len ← fieldTerm <$> checkNoEscape len .field
      let ret ← inferTerm ret
      let ioSetInfo := .ioSetInfo ⟨keyTyp, keyInner, false⟩ idx len ret
      assert! (ret.escapes == false)
      pure ⟨ret.typ, ioSetInfo, false⟩
    | _ => throw $ .notAnArray keyTyp
  | .ioRead idx len => do
    if len = 0 then throw .emptyArray
    let idx ← fieldTerm <$> checkNoEscape idx .field
    let ioRead := .ioRead idx len
    pure ⟨.array .field len, ioRead, false⟩
  | .ioWrite data ret => do
    let (dataTyp, dataInner) ← inferNoEscape data
    match dataTyp with
    | .array dataEltTyp _ =>
      if dataEltTyp != .field then throw $ .typeMismatch .field dataEltTyp
      let ret ← inferTerm ret
      let ioWrite := .ioWrite ⟨dataTyp, dataInner, false⟩ ret
      assert! (ret.escapes == false)
      pure ⟨ret.typ, ioWrite, false⟩
    | _ => throw $ .notAnArray dataTyp
  | .u8BitDecomposition byte => do
    let byte ← fieldTerm <$> checkNoEscape byte .field
    let u8BitDecomposition := .u8BitDecomposition byte
    pure ⟨.array .field 8, u8BitDecomposition, false⟩
  | .u8ShiftLeft byte => do
    let byte ← fieldTerm <$> checkNoEscape byte .field
    let u8ShiftLeft := .u8ShiftLeft byte
    pure ⟨.field, u8ShiftLeft, false⟩
  | .u8ShiftRight byte => do
    let byte ← fieldTerm <$> checkNoEscape byte .field
    let u8ShiftRight := .u8ShiftRight byte
    pure ⟨.field, u8ShiftRight, false⟩
  | .u8Xor i j => do
    let i ← fieldTerm <$> checkNoEscape i .field
    let j ← fieldTerm <$> checkNoEscape j .field
    let u8Xor := .u8Xor i j
    pure ⟨.field, u8Xor, false⟩
  | .u8Add i j => do
    let i ← fieldTerm <$> checkNoEscape i .field
    let j ← fieldTerm <$> checkNoEscape j .field
    let u8Add := .u8Add i j
    pure ⟨.tuple #[.field, .field], u8Add, false⟩
  | .debug label term ret => do
    let term ← term.mapM inferTerm
    let ret ← inferTerm ret
    let debug := .debug label term ret
    assert! (ret.escapes == false)
    pure ⟨ret.typ, debug, false⟩
where
  /--
  Ensures that there are as many arguments and as expected types and that
  the types of the arguments are precisely those expected.
  -/
  checkArgsAndInputs func args inputs : CheckM (List TypedTerm) := do
    let lenArgs := args.length
    let lenInputs := inputs.length
    unless lenArgs == lenInputs do throw $ .wrongNumArgs func lenArgs lenInputs
    let pass := fun (arg, input) => do
      let inner ← checkNoEscape arg input
      pure ⟨input, inner, false⟩
    args.zip inputs |>.mapM pass
  checkArith a b := do
    let aInner ← checkNoEscape a .field
    let bInner ← checkNoEscape b .field
    pure (fieldTerm aInner, fieldTerm bInner)
  fieldTerm inner := ⟨.field, inner, false⟩

partial def checkNoEscape (term : Term) (typ : Typ) : CheckM TypedTermInner := do
  let (typ', inner) ← inferNoEscape term
  unless typ == typ' do throw $ .typeMismatch typ typ'
  pure inner

partial def inferNoEscape (term : Term) : CheckM (Typ × TypedTermInner) := do
  let typedTerm ← inferTerm term
  if typedTerm.escapes then throw .illegalReturn
  pure (typedTerm.typ, typedTerm.inner)

partial def inferData : Data → CheckM (Typ × TypedTermInner)
  | .field g => pure (.field, .data (.field g))
  | .tuple terms => do
    let typsAndInners ← terms.mapM inferNoEscape
    let typs := typsAndInners.map Prod.fst
    let terms := typsAndInners.map fun (typ, inner) => ⟨typ, inner, false⟩
    pure (.tuple typs, .data (.tuple terms))
  | .array terms => do
    if h : terms.size > 0 then
      let (typ, firstInner) ← inferNoEscape terms[0]
      let mut typedTerms := Array.mkEmpty terms.size
        |>.push ⟨typ, firstInner, false⟩
      for term in terms[1:] do
        let inner ← checkNoEscape term typ
        typedTerms := typedTerms.push ⟨typ, inner, false⟩
      pure (.array typ terms.size, .data (.array typedTerms))
    else throw .emptyArray

/-- Infers the type of a 'match' expression and ensures its patterns and branches are valid. -/
partial def inferMatch (term : Term) (branches : List (Pattern × Term)) : CheckM TypedTerm := do
  let (termTyp, termInner) ← inferNoEscape term
  let term := ⟨termTyp, termInner, false⟩
  let init := ([], none)
  let (branches, typOpt) ← branches.foldrM (init := init) (checkBranch termTyp)
  match typOpt with
  | some (typ, escapes) => pure ⟨typ, .match term branches, escapes⟩
  | none => throw .emptyMatch
where
  checkBranch patTyp branchData acc := do
    let (pat, branch) := branchData
    let (typedBranches, currentTypOpt) := acc
    let bindings ← checkPattern pat patTyp
    withReader (bindIdents bindings) (match currentTypOpt with
      | none => do
        let typedBranch ← inferTerm branch
        pure (typedBranches.cons (pat, typedBranch), some (typedBranch.typ, typedBranch.escapes))
      | some (matchTyp, matchEscapes) => do
        let typedBranch ← inferTerm branch
        let typedBranches := typedBranches.cons (pat, typedBranch)
        if typedBranch.escapes then
          pure (typedBranches, currentTypOpt)
        else if matchEscapes then
          pure (typedBranches, some (typedBranch.typ, false))
        else
          -- Neither branch escapes so their types must match
          unless (matchTyp == typedBranch.typ) do throw $ .branchMismatch matchTyp typedBranch.typ
          pure (typedBranches, currentTypOpt))

/-- Checks that a pattern matches a given type and collects its bindings. -/
partial def checkPattern (pat : Pattern) (typ : Typ) : CheckM $ List (Local × Typ) := do
  let binds ← aux pat typ
  let locals := binds.map Prod.fst
  unless (locals == locals.eraseDups) do throw $ .duplicatedBind pat
  pure binds
where
  aux pat typ := match (pat, typ) with
    | (.var var, _) => pure [(var, typ)]
    | (.wildcard, _)
    | (.field _, .field) => pure []
    | (.tuple pats, .tuple typs) => do
      unless pats.size == typs.size do throw $ .incompatiblePattern pat typ
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
    | (.array pats, .array innerTyp n) => do
      unless pats.size == n do throw $ .incompatiblePattern pat typ
      pats.foldlM (init := []) fun acc pat => acc.append <$> aux pat innerTyp
    | (.ref funcName [], typ@(.function ..)) => do
      let ctx ← read
      let some (.function function) := ctx.decls.getByKey funcName | throw $ .incompatiblePattern pat typ
      let typ' := .function (function.inputs.map Prod.snd) function.output
      unless typ == typ' do throw $ .typeMismatch typ typ'
      pure []
    | (.ref constrRef pats, .dataType dataTypeRef) => do
      let ctx ← read
      let some (.dataType dataType) := ctx.decls.getByKey dataTypeRef | unreachable!
      let some (.constructor dataType' constr) := ctx.decls.getByKey constrRef | throw $ .notAConstructor constrRef
      unless dataType == dataType' do throw $ .incompatiblePattern pat typ
      let typs := constr.argTypes
      let lenPats := pats.length
      let lenTyps := typs.length
      unless lenPats == lenTyps do throw $ .wrongNumArgs constrRef lenPats lenTyps
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
    | (.or pat pat', _) => do
      let bind ← aux pat typ
      let bind' ← aux pat' typ
      if bind != bind' then throw $ .differentBindings bind bind' else pure bind
    | (.pointer pat, .pointer typ) => aux pat typ
    | _ => throw $ .incompatiblePattern pat typ

partial def inferTuple (term : Term) : CheckM (Array Typ × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  let .tuple typs := typ | throw $ .notATuple typ
  pure (typs, inner)

partial def inferArray (term : Term) : CheckM (Typ × Nat × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  let .array typ n := typ | throw $ .notAnArray typ
  pure (typ, n, inner)
end

def getFunctionContext (function : Function) (decls : Decls) : CheckContext :=
  {
    decls,
    varTypes := .ofList function.inputs
    returnType := function.output
    unconstrained := function.unconstrained
  }

/--
Ensures that all declarations are wellformed by checking that every datatype reference
points to an actual datatype in the toplevel.

Note: it's assumed that all constructor declarations are properly extracted from the
original datatypes.
-/
partial def wellFormedDecls (decls : Decls) : Except CheckError Unit := do
  let mut visited := default
  for (_, decl) in decls.pairs do
    match EStateM.run (wellFormedDecl decl) visited with
    | .error e _ => throw e
    | .ok () visited' => visited := visited'
where
  wellFormedDecl : Declaration → EStateM CheckError (Std.HashSet Global) Unit
    | .dataType dataType => do
      let map ← get
      if !map.contains dataType.name then
        set $ map.insert dataType.name
        dataType.constructors.flatMap (·.argTypes) |>.forM wellFormedType
    | .function function => do
      wellFormedType function.output
      function.inputs.forM fun (_, typ) => wellFormedType typ
    -- No need to check constructors because they come from datatype declarations.
    | .constructor .. => pure ()
  wellFormedType : Typ → EStateM CheckError (Std.HashSet Global) Unit
    | .tuple typs => typs.forM wellFormedType
    | .pointer pointerTyp => wellFormedType pointerTyp
    | .dataType dataTypeRef => match decls.getByKey dataTypeRef with
      | some (.dataType _) => pure ()
      | some _ => throw $ .notADataType dataTypeRef
      | none => throw $ .undefinedGlobal dataTypeRef
    | _ => pure ()

/-- Checks a function to ensure its body's type matches its declared output type. -/
def checkFunction (function : Function) : CheckM TypedFunction := do
  let body ← inferTerm function.body
  unless body.escapes do
    unless body.typ == function.output do throw $ .typeMismatch body.typ function.output
  pure ⟨function.name, function.inputs, function.output, body, function.unconstrained⟩

end Aiur
