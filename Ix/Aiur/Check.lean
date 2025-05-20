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
  | nonNumeric : Typ → CheckError
  | wrongNumArgs : Global → Nat → Nat → CheckError
  | notATuple : Typ → CheckError
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

def Primitive.type : Primitive → PrimitiveType
  | u1 _ => .u1
  | u8 _ => .u8
  | u16 _ => .u16
  | u32 _ => .u32
  | u64 _ => .u64

/-- Extend context with locally bound variables. -/
def bindIdents (bindings : List (Local × Typ)) (ctx : CheckContext) : CheckContext :=
  { ctx with varTypes := ctx.varTypes.insertMany bindings }

mutual
partial def inferTerm : Term → CheckM TypedTerm
  | .var x => do
    -- Retrieves and returns the variable type from the context.
    let ctx ← read
    match ctx.varTypes[x]? with
    | some t => pure $ .mk (.evaluates t) (.var x)
    | none =>
      let Local.str localName := x | unreachable!
      let typ := .evaluates (← refLookup (Global.init localName))
      pure $ .mk typ (.var x)
  | .ref x => do
    let typ := .evaluates (← refLookup x)
    pure $ .mk typ (.ref x)
  | .ret term => do
    -- Ensures that the type of the returned term matches the expected return type.
    -- The term is not allowed to have a (nested) return.
    -- Returning the type of the term is not necessary because it's already in the context.
    let ctx ← read
    let inner ← checkNoEscape term ctx.returnType
    pure $ .mk .escapes inner
  | .data data => do
    let (typ, inner) ← inferData data
    pure $ .mk (.evaluates typ) inner
  | .let pat expr body => do
    -- Returns the type of the body, inferred in the context extended with the bound variable type.
    -- The bound variable is ensured not to escape.
    let (exprTyp, exprInner) ← inferNoEscape expr
    let expr' := .mk (.evaluates exprTyp) exprInner
    let bindings ← checkPattern pat exprTyp
    let body' ← withReader (bindIdents bindings) (inferTerm body)
    pure $ .mk body'.typ (.let pat expr' body')
  | .match term branches => inferMatch term branches
  | .if b t f => do
    -- Ensures that the type of the conditional is a number and the type of both branches are equal,
    -- unless one of them escapes.
    -- The returned type is the type of the branches.
    let (numTyp, numInner) ← inferNumber b
    let inferredNum := .mk (.evaluates numTyp) numInner
    let inferredT ← inferTerm t
    let inferredF ← inferTerm f
    let inner := .if inferredNum inferredT inferredF
    match (inferredT.typ, inferredF.typ) with
    | (.evaluates typT, .evaluates typF) => do
      unless typT == typF do throw $ .typeMismatch typT typF
      pure $ .mk inferredT.typ inner
    | (.evaluates _, .escapes) => pure $ .mk inferredT.typ inner
    | _ => pure $ .mk inferredF.typ inner
  | .app func@(⟨.str .anonymous unqualifiedFunc⟩) args => do
    -- Ensures the function exists in the context and that the arguments, which aren't allowed to
    -- escape, match the function's input types. Returns the function's output type.
    let ctx ← read
    match ctx.varTypes[Local.str unqualifiedFunc]? with
    | some (.function inputs output) => do
      let args ← checkArgsAndInputs func args inputs
      pure $ .mk (.evaluates output) (.app func args)
    | some _ => throw $ .notAFunction func
    | none => match ctx.decls.getByKey func with
      | some (.function function) => do
        let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
        pure $ .mk (.evaluates function.output) (.app func args)
      | some (.constructor dataType constr) => do
        let args ← checkArgsAndInputs func args constr.argTypes
        pure $ .mk (.evaluates (.dataType dataType.name)) (.app func args)
      | _ => throw $ .cannotApply func
  | .app func args => do
    -- Only checks global map if it is not unqualified
    let ctx ← read
    match ctx.decls.getByKey func with
    | some (.function function) =>
      let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
      pure $ .mk (.evaluates function.output) (.app func args)
    | some (.constructor dataType constr) => do
      let args ← checkArgsAndInputs func args constr.argTypes
      pure $ .mk (.evaluates (.dataType dataType.name)) (.app func args)
    | _ => throw $ .cannotApply func
  | .preimg func@(⟨.str .anonymous unqualifiedFunc⟩) arg => do
    -- Checks if the type of the argument, which isn't allowed to escape, matches the
    -- output type of the function, and infers the type of the function's inputs as a tuple.
    -- Errors if the function isn't found in the context.
    let ctx ← read
    match ctx.varTypes[Local.str unqualifiedFunc]? with
    | some (.function inputs output) => do
      let argInner ← checkNoEscape arg output
      let arg' := .mk (.evaluates output) argInner
      pure $ .mk (.evaluates (.tuple inputs.toArray)) (.preimg func arg')
    | some _ => throw $ .notAFunction func
    | none => match ctx.decls.getByKey func with
      | some (.function function) => do
        let argInner ← checkNoEscape arg function.output
        let arg' := .mk (.evaluates function.output) argInner
        let inpTyp := function.inputs.map Prod.snd
        pure $ .mk (.evaluates (.tuple inpTyp.toArray)) (.preimg func arg')
      | some _ => throw $ .notAFunction func
      | _ => throw $ .unboundVariable func
  | .preimg func arg => do
    -- Only checks global map if it is not unqualified
    let ctx ← read
    match ctx.decls.getByKey func with
    | some (.function function) => do
      let argInner ← checkNoEscape arg function.output
      let arg' := .mk (.evaluates function.output) argInner
      let inpTyp := function.inputs.map Prod.snd
      pure $ .mk (.evaluates (.tuple inpTyp.toArray)) (.preimg func arg')
    | some _ => throw $ .notAFunction func
    | _ => throw $ .unboundVariable func
  | .xor a b => do
    let (typ, aInner) ← inferNumber a
    let bInner ← checkNoEscape b typ
    let ctxTyp := .evaluates typ
    let a := .mk ctxTyp aInner
    let b := .mk ctxTyp bInner
    pure $ .mk ctxTyp (.xor a b)
  | .and a b => do
    let (typ, aInner) ← inferNumber a
    let bInner ← checkNoEscape b typ
    let ctxTyp := .evaluates typ
    let a := .mk ctxTyp aInner
    let b := .mk ctxTyp bInner
    pure $ .mk ctxTyp (.and a b)
  | .get tup i => do
    let (typs, tupInner) ← inferTuple tup
    if i < typs.size then
      let typ := typs[i]!
      let tup := .mk (.evaluates (.tuple typs)) tupInner
      pure $ .mk (.evaluates typ) (.get tup i)
    else
      throw $ .indexOoB i
  | .slice tup i j =>
    -- Retrieves the types of elements in a tuple by a range (checked to be non-negative) and
    -- returns them encoded in a `Typ.tuple`. Errors if the index is out of bounds.
    if j < i then throw $ .negativeRange i j else do
    let (typs, tupInner) ← inferTuple tup
    if i < typs.size then
      let slice := typs.drop i |>.take (j - i)
      let tup := .mk (.evaluates (.tuple typs)) tupInner
      pure $ .mk (.evaluates (.tuple slice)) (.slice tup i j)
    else
      throw $ .rangeOoB i j
  | .store term => do
    -- Infers the type of the term and returns it, wrapped by a pointer type.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    let store := .store (.mk (.evaluates typ) inner)
    pure $ .mk (.evaluates (.pointer typ)) store
  | .load term => do
    -- Ensures that the the type of the term is a pointer type and returns the unwrapped type.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    match typ with
    | .pointer innerTyp =>
      let load := .load (.mk (.evaluates typ) inner)
      pure $ .mk (.evaluates innerTyp) load
    | _ => throw $ .notAPointer typ
  | .pointerAsU64 term => do
    -- Infers the type of the term, which must be a pointer, but returns `.u64`, as in a cast.
    -- The term is not allowed to early return.
    let (typ, inner) ← inferNoEscape term
    match typ with
    | .pointer _ =>
      let asU64 := .pointerAsU64 (.mk (.evaluates typ) inner)
      pure $ .mk (.evaluates (.primitive .u64)) asU64
    | _ => throw $ .notAPointer typ
  | .ann typ term => do
    let inner ← checkNoEscape term typ
    pure $ .mk (.evaluates typ) inner
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
      pure $ .mk (.evaluates input) inner
    args.zip inputs |>.mapM pass

partial def checkNoEscape (term : Term) (typ : Typ) : CheckM TypedTermInner := do
  let (typ', inner) ← inferNoEscape term
  unless typ == typ' do throw $ .typeMismatch typ typ'
  pure inner

partial def inferNoEscape (term : Term) : CheckM (Typ × TypedTermInner) := do
  let typedTerm ← inferTerm term
  match typedTerm.typ with
  | .escapes => throw .illegalReturn
  | .evaluates type => pure (type, typedTerm.inner)

partial def inferData : Data → CheckM (Typ × TypedTermInner)
  | .primitive prim => pure (.primitive prim.type, .data (.primitive prim))
  | .tuple terms => do
    let typsAndInners ← terms.mapM inferNoEscape
    let typs := typsAndInners.map Prod.fst
    let terms := typsAndInners.map fun (typ, inner) => TypedTerm.mk (.evaluates typ) inner
    pure (.tuple typs, .data (.tuple terms))

/-- Infers the type of a 'match' expression and ensures its patterns and branches are valid. -/
partial def inferMatch (term : Term) (branches : List (Pattern × Term)) : CheckM TypedTerm := do
  if branches.isEmpty then throw .emptyMatch
  let (termTyp, termInner) ← inferNoEscape term
  let term := .mk (.evaluates termTyp) termInner
  let init := ([], .escapes)
  let (branches, typ) ← branches.foldrM (init := init) (checkBranch termTyp)
  pure $ .mk typ (.match term branches)
where
  checkBranch patTyp branchData acc := do
  let (pat, branch) := branchData
  let (typedBranches, currentTyp) := acc
  let bindings ← checkPattern pat patTyp
  withReader (bindIdents bindings) (match currentTyp with
    | .escapes => do
      let typedBranch ← inferTerm branch
      pure (typedBranches.cons (pat, typedBranch), typedBranch.typ)
    | .evaluates matchTyp => do
      -- Some branch didn't escape, so if this branch doesn't escape it must have the same type
      -- as the previous non-escaping branch.
      let typedBranch ← inferTerm branch
      let typedBranches := typedBranches.cons (pat, typedBranch)
      match typedBranch.typ with
      | .escapes => pure (typedBranches, currentTyp)
      | .evaluates branchTyp =>
        -- This branch doesn't escape so its type must match the type of the previous non-escaping branch.
        unless (matchTyp == branchTyp) do throw $ .branchMismatch matchTyp branchTyp
        pure (typedBranches, currentTyp))

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
    | (.primitive (.u1 _), .primitive .u1)
    | (.primitive (.u8 _), .primitive .u8)
    | (.primitive (.u16 _), .primitive .u16)
    | (.primitive (.u32 _), .primitive .u32)
    | (.primitive (.u64 _), .primitive .u64) => pure []
    | (.tuple pats, .tuple typs) => do
      unless pats.size != typs.size do throw $ .incompatiblePattern pat typ
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
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
    | _ => throw $ .incompatiblePattern pat typ

partial def inferNumber (term : Term) : CheckM (Typ × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  match typ with
  | .primitive .u1
  | .primitive .u8
  | .primitive .u16
  | .primitive .u32
  | .primitive .u64 => pure (typ, inner)
  | _ => throw $ .nonNumeric typ

partial def inferTuple (term : Term) : CheckM (Array Typ × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  match typ with
  | .tuple typs => pure (typs, inner)
  | _ => throw $ .notATuple typ
end

def getFunctionContext (function : Function) (decls : Decls) : CheckContext :=
  {
    decls,
    varTypes := .ofList function.inputs
    returnType := function.output
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
  if let .evaluates typ := body.typ then
    unless typ == function.output do throw $ .typeMismatch typ function.output
  pure { name := function.name, inputs := function.inputs, output := function.output, body := body }

/--
Checks all top-level definitions in a program, ensuring they are valid and return the map
of declarations.
-/
def checkToplevel (toplevel : Toplevel) : Except CheckError TypedDecls := do
  let decls ← toplevel.mkDecls
  wellFormedDecls decls
  decls.pairs.foldlM (init := default) fun typedDecls (name, decl) => match decl with
    | .constructor d c => pure $ typedDecls.insert name (.constructor d c)
    | .dataType d => pure $ typedDecls.insert name (.dataType d)
    | .function f => do
      let f ← (checkFunction f) (getFunctionContext f decls)
      pure $ typedDecls.insert name (.function f)

end Aiur
