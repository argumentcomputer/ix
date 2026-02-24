module
public import Ix.Aiur.Term
public import Std.Data.HashSet

public section

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

def fieldTerm (t : TypedTermInner) : TypedTerm := ⟨.field, t, false⟩

mutual
partial def inferTerm (t : Term) : CheckM TypedTerm := match t with
  | .unit => pure ⟨.unit, .unit, false⟩
  | .var x => inferVariable x
  | .ref x => do
    pure ⟨← refLookup x, .ref x, false⟩
  | .ret term => inferReturn term
  | .data data => inferData data
  | .let pat expr body => inferLet pat expr body
  | .match term branches => inferMatch term branches
  | .app func args => inferApplication func args
  | .ann typ term => do
    pure ⟨typ, ← checkNoEscape term typ, false⟩
  | .proj tup i => inferProj tup i
  | .get arr i => inferGet arr i
  | .slice arr i j => inferSlice arr i j
  | .set arr i val => inferSet arr i val
  | .store term => inferStore term
  | .load term => inferLoad term
  | .ptrVal term => inferPtrVal term
  | .eqZero a => inferUnop a .eqZero .field
  | .add a b => inferBinop a b .add .field
  | .sub a b => inferBinop a b .sub .field
  | .mul a b => inferBinop a b .mul .field
  | .u8ShiftLeft a => inferUnop a .u8ShiftLeft .field
  | .u8ShiftRight a => inferUnop a .u8ShiftRight .field
  | .u8BitDecomposition a => inferUnop a .u8BitDecomposition (.array .field 8)
  | .u8Xor a b => inferBinop a b .u8Xor .field
  | .u8And a b => inferBinop a b .u8And .field
  | .u8Or a b => inferBinop a b .u8Or .field
  | .u8Add a b => inferBinop a b .u8Add (.tuple #[.field, .field])
  | .u8Sub a b => inferBinop a b .u8Sub (.tuple #[.field, .field])
  | .u8LessThan a b => inferBinop a b .u8LessThan .field
  | .ioGetInfo key => inferIoGetInfo key
  | .ioSetInfo key idx len ret => inferIoSetInfo key idx len ret
  | .ioRead idx len => inferIoRead idx len
  | .ioWrite data ret => inferIoWrite data ret
  | .assertEq a b ret => inferAssertEq a b ret
  | .debug label term ret => inferDebug label term ret

partial def checkNoEscape (term : Term) (typ : Typ) : CheckM TypedTermInner := do
  let (typ', inner) ← inferNoEscape term
  unless typ == typ' do throw $ .typeMismatch typ typ'
  pure inner

partial def inferNoEscape (term : Term) : CheckM (Typ × TypedTermInner) := do
  let typedTerm ← inferTerm term
  if typedTerm.escapes then throw .illegalReturn
  pure (typedTerm.typ, typedTerm.inner)

partial def inferUnop
  (a : Term)
  (op : TypedTerm → TypedTermInner)
  (typ : Typ) :
  CheckM TypedTerm := do
  let a ← fieldTerm <$> checkNoEscape a .field
  pure ⟨typ, op a, false⟩

partial def inferBinop
  (a : Term)
  (b : Term)
  (op : TypedTerm → TypedTerm → TypedTermInner)
  (typ : Typ) :
  CheckM TypedTerm := do
  let a ← fieldTerm <$> checkNoEscape a .field
  let b ← fieldTerm <$> checkNoEscape b .field
  pure ⟨typ, op a b, false⟩

partial def inferProj (tup : Term) (i : Nat) : CheckM TypedTerm := do
  let (typs, tupInner) ← inferTuple tup
  if h : i < typs.size then
    let typ := typs[i]
    let tup := ⟨.tuple typs, tupInner, false⟩
    pure ⟨typ, .proj tup i, false⟩
  else
    throw $ .indexOoB i

partial def inferGet (arr : Term) (i : Nat) : CheckM TypedTerm := do
  let (typ, n, inner) ← inferArray arr
  if i ≥ n then
    throw $ .indexOoB i
  else
    let arr := ⟨.array typ n, inner, false⟩
    pure ⟨typ, .get arr i, false⟩

partial def inferSlice (arr : Term) (i j : Nat) : CheckM TypedTerm :=
  if j < i then throw $ .negativeRange i j else do
    let (typ, n, inner) ← inferArray arr
    if j ≤ n then
      let arr := ⟨.array typ n, inner, false⟩
      pure ⟨.array typ (j - i), .slice arr i j, false⟩
    else
      throw $ .rangeOoB i j

partial def inferSet (arr : Term) (i : Nat) (val : Term) : CheckM TypedTerm := do
  let (typ, n, inner) ← inferArray arr
  if i ≥ n then
    throw $ .indexOoB i
  else
    let val ← checkNoEscape val typ
    let arrTyp := .array typ n
    let arr := ⟨arrTyp, inner, false⟩
    let val := ⟨typ, val, false⟩
    pure ⟨arrTyp, .set arr i val, false⟩

partial def inferStore (term : Term) : CheckM TypedTerm := do
  let (typ, inner) ← inferNoEscape term
  let store := .store ⟨typ, inner, false⟩
  pure ⟨.pointer typ, store, false⟩

partial def inferLoad (term : Term) : CheckM TypedTerm := do
  let (typ, inner) ← inferNoEscape term
  match typ with
  | .pointer innerTyp =>
    let load := .load ⟨typ, inner, false⟩
    pure ⟨innerTyp, load, false⟩
  | _ => throw $ .notAPointer typ

partial def inferPtrVal (term : Term) : CheckM TypedTerm := do
  let (typ, inner) ← inferNoEscape term
  match typ with
  | .pointer _ => pure $ fieldTerm (.ptrVal ⟨typ, inner, false⟩)
  | _ => throw $ .notAPointer typ

partial def inferIoGetInfo (key : Term) : CheckM TypedTerm := do
  let (typ, keyInner) ← inferNoEscape key
  match typ with
  | .array .. =>
    let ioGetInfo := .ioGetInfo ⟨typ, keyInner, false⟩
    pure ⟨.tuple #[.field, .field], ioGetInfo, false⟩
  | _ => throw $ .notAnArray typ

partial def inferIoSetInfo (key idx len ret : Term) : CheckM TypedTerm := do
  let (keyTyp, keyInner) ← inferNoEscape key
  match keyTyp with
  | .array keyEltTyp _ =>
    if keyEltTyp != .field then throw $ .typeMismatch .field keyEltTyp
    let idx ← fieldTerm <$> checkNoEscape idx .field
    let len ← fieldTerm <$> checkNoEscape len .field
    let ret ← inferTerm ret
    let ioSetInfo := .ioSetInfo ⟨keyTyp, keyInner, false⟩ idx len ret
    pure ⟨ret.typ, ioSetInfo, ret.escapes⟩
  | _ => throw $ .notAnArray keyTyp

partial def inferIoRead (idx : Term) (len : Nat) : CheckM TypedTerm := do
  if len = 0 then throw .emptyArray
  let idx ← fieldTerm <$> checkNoEscape idx .field
  let ioRead := .ioRead idx len
  pure ⟨.array .field len, ioRead, false⟩

partial def inferIoWrite (data ret : Term) : CheckM TypedTerm := do
  let (dataTyp, dataInner) ← inferNoEscape data
  match dataTyp with
  | .array dataEltTyp _ =>
    if dataEltTyp != .field then throw $ .typeMismatch .field dataEltTyp
    let ret ← inferTerm ret
    let ioWrite := .ioWrite ⟨dataTyp, dataInner, false⟩ ret
    pure ⟨ret.typ, ioWrite, ret.escapes⟩
  | _ => throw $ .notAnArray dataTyp

partial def inferVariable (x : Local) : CheckM TypedTerm := do
  let ctx ← read
  match ctx.varTypes[x]? with
  | some t => pure ⟨t, .var x, false⟩
  | none =>
    let Local.str localName := x | unreachable!
    let typ ← refLookup (Global.init localName)
    pure ⟨typ, .var x, false⟩

partial def inferReturn (term : Term) : CheckM TypedTerm := do
  let ctx ← read
  let inner ← checkNoEscape term ctx.returnType
  pure ⟨ctx.returnType, inner, true⟩

partial def inferLet (pat : Pattern) (expr : Term) (body : Term) : CheckM TypedTerm := do
  let (exprTyp, exprInner) ← inferNoEscape expr
  let expr' := ⟨exprTyp, exprInner, false⟩
  let bindings ← checkPattern pat exprTyp
  let body' ← withReader (bindIdents bindings) (inferTerm body)
  pure ⟨body'.typ, .let pat expr' body', body'.escapes⟩

partial def inferUnqualifiedApp (func : Global) (unqualifiedFunc : String) (args : List Term) : CheckM TypedTerm := do
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
where
  checkArgsAndInputs func args inputs : CheckM (List TypedTerm) := do
    let lenArgs := args.length
    let lenInputs := inputs.length
    unless lenArgs == lenInputs do throw $ .wrongNumArgs func lenArgs lenInputs
    let pass := fun (arg, input) => do
      let inner ← checkNoEscape arg input
      pure ⟨input, inner, false⟩
    args.zip inputs |>.mapM pass

partial def inferQualifiedApp (func : Global) (args : List Term) : CheckM TypedTerm := do
  let ctx ← read
  match ctx.decls.getByKey func with
  | some (.function function) =>
    let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
    pure ⟨function.output, .app func args, false⟩
  | some (.constructor dataType constr) =>
    let args ← checkArgsAndInputs func args constr.argTypes
    pure ⟨.dataType dataType.name, .app func args, false⟩
  | _ => throw $ .cannotApply func
where
  checkArgsAndInputs func args inputs : CheckM (List TypedTerm) := do
    let lenArgs := args.length
    let lenInputs := inputs.length
    unless lenArgs == lenInputs do throw $ .wrongNumArgs func lenArgs lenInputs
    let pass := fun (arg, input) => do
      let inner ← checkNoEscape arg input
      pure ⟨input, inner, false⟩
    args.zip inputs |>.mapM pass

partial def inferApplication (func : Global) (args : List Term) : CheckM TypedTerm :=
  match func.toName with
  | .str .anonymous unqualifiedFunc => inferUnqualifiedApp func unqualifiedFunc args
  | _ => inferQualifiedApp func args

partial def inferAssertEq (a b ret : Term) : CheckM TypedTerm := do
  let (typ, a) ← inferNoEscape a
  let b ← checkNoEscape b typ
  let ret ← inferTerm ret
  let assertEq := .assertEq ⟨typ, a, false⟩ ⟨typ, b, false⟩ ret
  pure ⟨ret.typ, assertEq, ret.escapes⟩

partial def inferDebug (label : String) (term : Option Term) (ret : Term) : CheckM TypedTerm := do
  let term ← term.mapM inferTerm
  let ret ← inferTerm ret
  let debug := .debug label term ret
  pure ⟨ret.typ, debug, ret.escapes⟩

partial def inferData : Data → CheckM TypedTerm
  | .field g => pure ⟨.field, .data (.field g), false⟩
  | .tuple terms => do
    let typsAndInners ← terms.mapM inferNoEscape
    let typs := typsAndInners.map Prod.fst
    let terms := typsAndInners.map fun (typ, inner) => ⟨typ, inner, false⟩
    pure ⟨.tuple typs, .data (.tuple terms), false⟩
  | .array terms => do
    if h : terms.size > 0 then
      let (typ, firstInner) ← inferNoEscape terms[0]
      let mut typedTerms := Array.mkEmpty terms.size
        |>.push ⟨typ, firstInner, false⟩
      for term in terms[1:] do
        let inner ← checkNoEscape term typ
        typedTerms := typedTerms.push ⟨typ, inner, false⟩
      pure ⟨.array typ terms.size, .data (.array typedTerms), false⟩
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

end
