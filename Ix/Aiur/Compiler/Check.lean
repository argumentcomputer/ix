module
public import Ix.Aiur.TypedTerm
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace Aiur

inductive CheckError
  | duplicatedDefinition : Global → CheckError
  | unboundGlobal : Global → CheckError
  | unboundLocal : Local → CheckError
  | notAConstructor : Global → CheckError
  | notAValue : Global → CheckError
  | notAFunction : Global → CheckError
  | cannotApply : Global → CheckError
  | notADataType : Global → CheckError
  | wrongNumTypeArgs : Global → Nat → Nat → CheckError
  | duplicatedTypeParam : Global → String → CheckError
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
  | typeAliasCycle : Global → CheckError
  | unconstrainedConstructor : Global → CheckError
  | infiniteType : Nat → Typ → CheckError
  | unresolvedMVar : Nat → CheckError
  deriving Repr

instance : ToString CheckError where
  toString e := repr e |>.pretty

/-- Apply a type-parameter substitution to a type. -/
partial def Typ.instantiate (subst : Global → Option Typ) : Typ → Typ
  | .unit => .unit
  | .field => .field
  | .tuple ts => .tuple (ts.map (Typ.instantiate subst))
  | .array t n => .array (Typ.instantiate subst t) n
  | .pointer t => .pointer (Typ.instantiate subst t)
  | .ref g => (subst g).getD (.ref g)
  | .app g args => .app g (args.map (Typ.instantiate subst))
  | .function ins out => .function (ins.map (Typ.instantiate subst)) (Typ.instantiate subst out)
  | .mvar n => .mvar n

/-- Build a substitution from params ↦ type-arguments. -/
def mkParamSubst (params : List String) (args : Array Typ) : Global → Option Typ :=
  let m : Std.HashMap Global Typ := (params.zip args.toList).foldl
    (fun m (p, t) => m.insert (Global.init p) t) {}
  fun g => m[g]?

/--
Eagerly expands type aliases, building the aliasMap on demand and detecting cycles.
Handles both `.ref g` (to non-parameterized alias) and `.app g args` (to parameterized alias).
-/
partial def expandTypeM (visited : Std.HashSet Global) (toplevelAliases : Array TypeAlias) :
    Typ → StateT (Std.HashMap Global Typ) (Except CheckError) Typ
  | .unit => pure .unit
  | .field => pure .field
  | .pointer t => do pure $ .pointer (← expandTypeM visited toplevelAliases t)
  | .function inputs output => do
    let inputs' ← inputs.mapM (expandTypeM visited toplevelAliases)
    let output' ← expandTypeM visited toplevelAliases output
    pure $ .function inputs' output'
  | .tuple ts => do
    let ts' ← ts.mapM (expandTypeM visited toplevelAliases)
    pure $ .tuple ts'
  | .array t n => do
    let t' ← expandTypeM visited toplevelAliases t
    pure $ .array t' n
  | .app g args => do
    let args' ← args.mapM (expandTypeM visited toplevelAliases)
    if let some alias := toplevelAliases.find? (·.name == g) then
      if visited.contains g then
        throw $ .typeAliasCycle g
      if alias.params.length != args'.size then
        throw $ .wrongNumTypeArgs g alias.params.length args'.size
      let subst := mkParamSubst alias.params args'
      let instantiated := Typ.instantiate subst alias.expansion
      expandTypeM (visited.insert g) toplevelAliases instantiated
    else
      pure $ .app g args'
  | .ref g => do
    let aliasMap ← get
    -- Check if already expanded (cache)
    if let some expanded := aliasMap[g]? then
      return expanded
    -- Check if it's an alias (non-parameterized only here)
    if let some (alias : TypeAlias) := toplevelAliases.find? (·.name == g) then
      if visited.contains g then
        throw $ .typeAliasCycle g
      if !alias.params.isEmpty then
        throw $ .wrongNumTypeArgs g alias.params.length 0
      let expanded ← expandTypeM (visited.insert g) toplevelAliases alias.expansion
      set (aliasMap.insert g expanded)
      return expanded
    else
      pure $ .ref g
  | .mvar n => pure $ .mvar n

/-- Constructs a map of declarations from a toplevel, expanding all type aliases. -/
def Toplevel.mkDecls (toplevel : Toplevel) : Except CheckError Decls := do
  let mut allNames : Std.HashSet Global := {}
  for alias in toplevel.typeAliases do
    if allNames.contains alias.name then
      throw $ .duplicatedDefinition alias.name
    allNames := allNames.insert alias.name

  let initAliasMap := {}
  let (_, finalAliasMap) ← (toplevel.typeAliases.mapM fun (alias : TypeAlias) => do
    let expanded ← expandTypeM {} toplevel.typeAliases alias.expansion
    modify fun (aliasMap : Std.HashMap Global Typ) => aliasMap.insert alias.name expanded
  ).run initAliasMap

  let expandTyp (typ : Typ) : Except CheckError Typ :=
    (expandTypeM {} toplevel.typeAliases typ).run' finalAliasMap

  let mut decls : Decls := default
  for function in toplevel.functions do
    if allNames.contains function.name then
      throw $ .duplicatedDefinition function.name
    allNames := allNames.insert function.name
    let inputs' ← function.inputs.mapM fun (loc, typ) => do
      let typ' ← expandTyp typ
      pure (loc, typ')
    let output' ← expandTyp function.output
    let function' := { function with inputs := inputs', output := output' }
    decls := decls.insert function.name (.function function')

  for dataType in toplevel.dataTypes do
    if allNames.contains dataType.name then
      throw $ .duplicatedDefinition dataType.name
    allNames := allNames.insert dataType.name
    let mut constructors : List Constructor := []
    for ctor in dataType.constructors do
      let argTypes' ← ctor.argTypes.mapM expandTyp
      constructors := constructors.concat { ctor with argTypes := argTypes' }
    let dataType' := { dataType with constructors }
    decls := decls.insert dataType.name (.dataType dataType')
    for ctor in constructors do
      let ctorName := dataType.name.pushNamespace ctor.nameHead
      if allNames.contains ctorName then
        throw $ .duplicatedDefinition ctorName
      allNames := allNames.insert ctorName
      decls := decls.insert ctorName (.constructor dataType' ctor)

  pure decls

/-! ## Inference monad and unification -/

structure CheckContext where
  decls : Decls
  varTypes : Std.HashMap Local Typ
  returnType : Typ
  typeParams : List String

structure CheckState where
  nextMVar : Nat := 0
  mvarSubst : Std.HashMap Nat Typ := {}

abbrev CheckM := ReaderT CheckContext (StateT CheckState (Except CheckError))

def freshMVar : CheckM Typ := do
  let idx := (← get).nextMVar
  modify fun s => { s with nextMVar := s.nextMVar + 1 }
  pure $ .mvar idx

/-- Walks the mvar substitution chain. -/
partial def walkTyp : Typ → CheckM Typ
  | .mvar id => do
    match (← get).mvarSubst[id]? with
    | some t => walkTyp t
    | none => pure (.mvar id)
  | t => pure t

/-- Occurs check: does mvar `id` appear in type `t`? -/
partial def occursIn (id : Nat) : Typ → CheckM Bool
  | .mvar id' => do
    match (← get).mvarSubst[id']? with
    | some t => occursIn id t
    | none => pure (id == id')
  | .tuple ts => ts.anyM (occursIn id)
  | .array t _ => occursIn id t
  | .pointer t => occursIn id t
  | .function ins out => do
    if ← ins.anyM (occursIn id) then pure true else occursIn id out
  | .app _ args => args.anyM (occursIn id)
  | _ => pure false

/-- Bind an mvar to a type, with occurs check. -/
def bindMVar (id : Nat) (t : Typ) : CheckM Unit := do
  if ← occursIn id t then throw $ .infiniteType id t
  modify fun s => { s with mvarSubst := s.mvarSubst.insert id t }

/-- First-order unification. Returns `true` on success, `false` on mismatch. -/
partial def unifyTyp (t1 t2 : Typ) : CheckM Bool := do
  let t1 ← walkTyp t1
  let t2 ← walkTyp t2
  match t1, t2 with
  | .mvar a, .mvar b =>
    if a == b then pure true else do bindMVar a (.mvar b); pure true
  | .mvar a, _ => do bindMVar a t2; pure true
  | _, .mvar b => do bindMVar b t1; pure true
  | .unit, .unit | .field, .field => pure true
  | .tuple ts1, .tuple ts2 =>
    if ts1.size != ts2.size then pure false else
      ts1.zip ts2 |>.allM fun (x, y) => unifyTyp x y
  | .array t1' n1, .array t2' n2 =>
    if n1 != n2 then pure false else unifyTyp t1' t2'
  | .pointer t1', .pointer t2' => unifyTyp t1' t2'
  | .ref g1, .ref g2 => pure (g1 == g2)
  | .function ins1 out1, .function ins2 out2 => do
    if ins1.length != ins2.length then pure false else
    let inOk ← ins1.zip ins2 |>.allM fun (x, y) => unifyTyp x y
    if !inOk then pure false else unifyTyp out1 out2
  | .app g1 a1, .app g2 a2 =>
    if g1 != g2 || a1.size != a2.size then pure false else
      a1.zip a2 |>.allM fun (x, y) => unifyTyp x y
  | _, _ => pure false

/-- Apply the current substitution, recursively resolving mvars. -/
partial def zonkTyp : Typ → CheckM Typ
  | .mvar id => do
    match (← get).mvarSubst[id]? with
    | some t => zonkTyp t
    | none => pure (.mvar id)
  | .tuple ts => do pure $ .tuple (← ts.mapM zonkTyp)
  | .array t n => do pure $ .array (← zonkTyp t) n
  | .pointer t => do pure $ .pointer (← zonkTyp t)
  | .function ins out => do pure $ .function (← ins.mapM zonkTyp) (← zonkTyp out)
  | .app g args => do pure $ .app g (← args.mapM zonkTyp)
  | t => pure t

/-- Create fresh mvars for each type parameter and build the substitution. -/
def instantiateParams (params : List String) : CheckM (Array Typ × (Global → Option Typ)) := do
  let mvars ← (params.toArray.mapM fun _ => freshMVar)
  pure (mvars, mkParamSubst params mvars)

/-! ## Type inference -/

/-- Retrieves the type of a global reference. -/
def refLookup (global : Global) : CheckM (Typ × Array Typ) := do
  let ctx ← read
  match ctx.decls.getByKey global with
  | some (.function function) =>
    if function.params.isEmpty then
      pure (.function (function.inputs.map Prod.snd) function.output, #[])
    else
      let (mvars, subst) ← instantiateParams function.params
      let inputs := function.inputs.map (Typ.instantiate subst ∘ Prod.snd)
      let output := Typ.instantiate subst function.output
      pure (.function inputs output, mvars)
  | some (.constructor dataType constructor) =>
    let args := constructor.argTypes
    unless args.isEmpty do (throw $ .wrongNumArgs global args.length 0)
    if dataType.params.isEmpty then
      pure (.ref dataType.name, #[])
    else
      let (mvars, _) ← instantiateParams dataType.params
      pure (.app dataType.name mvars, mvars)
  | some _ => throw $ .notAValue global
  | none => throw $ .unboundGlobal global

/-- Extend context with locally bound variables. -/
def bindIdents (bindings : List (Local × Typ)) (ctx : CheckContext) : CheckContext :=
  { ctx with varTypes := ctx.varTypes.insertMany bindings }

def fieldTerm (t : TypedTermInner) : TypedTerm := ⟨.field, t, false⟩

mutual
partial def inferTerm (t : Term) : CheckM TypedTerm := match t with
  | .unit => pure ⟨.unit, .unit, false⟩
  | .var x => inferVariable x
  | .ref x => do
    let (typ, tArgs) ← refLookup x
    pure ⟨typ, .ref x tArgs, false⟩
  | .ret term => inferReturn term
  | .data data => inferData data
  | .let pat expr body => inferLet pat expr body
  | .match term branches => inferMatch term branches
  | .app func args u => inferApplication func args u
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
  | .u32LessThan a b => inferBinop a b .u32LessThan .field
  | .ioGetInfo key => inferIoGetInfo key
  | .ioSetInfo key idx len ret => inferIoSetInfo key idx len ret
  | .ioRead idx len => inferIoRead idx len
  | .ioWrite data ret => inferIoWrite data ret
  | .assertEq a b ret => inferAssertEq a b ret
  | .debug label term ret => inferDebug label term ret

partial def checkNoEscape (term : Term) (typ : Typ) : CheckM TypedTermInner := do
  let (typ', inner) ← inferNoEscape term
  unless ← unifyTyp typ typ' do throw $ .typeMismatch typ typ'
  pure inner

partial def inferNoEscape (term : Term) : CheckM (Typ × TypedTermInner) := do
  let typedTerm ← inferTerm term
  if typedTerm.escapes then throw .illegalReturn
  pure (typedTerm.typ, typedTerm.inner)

partial def inferUnop (a : Term) (op : TypedTerm → TypedTermInner) (typ : Typ) :
    CheckM TypedTerm := do
  let a ← fieldTerm <$> checkNoEscape a .field
  pure ⟨typ, op a, false⟩

partial def inferBinop (a b : Term) (op : TypedTerm → TypedTerm → TypedTermInner) (typ : Typ) :
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
  match ← walkTyp typ with
  | .pointer innerTyp =>
    let load := .load ⟨typ, inner, false⟩
    pure ⟨innerTyp, load, false⟩
  | typ' => throw $ .notAPointer typ'

partial def inferPtrVal (term : Term) : CheckM TypedTerm := do
  let (typ, inner) ← inferNoEscape term
  match ← walkTyp typ with
  | .pointer _ => pure $ fieldTerm (.ptrVal ⟨typ, inner, false⟩)
  | typ' => throw $ .notAPointer typ'

partial def inferIoGetInfo (key : Term) : CheckM TypedTerm := do
  let (typ, keyInner) ← inferNoEscape key
  match ← walkTyp typ with
  | .array .. =>
    let ioGetInfo := .ioGetInfo ⟨typ, keyInner, false⟩
    pure ⟨.tuple #[.field, .field], ioGetInfo, false⟩
  | typ' => throw $ .notAnArray typ'

partial def inferIoSetInfo (key idx len ret : Term) : CheckM TypedTerm := do
  let (keyTyp, keyInner) ← inferNoEscape key
  match ← walkTyp keyTyp with
  | .array keyEltTyp _ =>
    unless ← unifyTyp keyEltTyp .field do throw $ .typeMismatch .field keyEltTyp
    let idx ← fieldTerm <$> checkNoEscape idx .field
    let len ← fieldTerm <$> checkNoEscape len .field
    let ret ← inferTerm ret
    let ioSetInfo := .ioSetInfo ⟨keyTyp, keyInner, false⟩ idx len ret
    pure ⟨ret.typ, ioSetInfo, ret.escapes⟩
  | typ' => throw $ .notAnArray typ'

partial def inferIoRead (idx : Term) (len : Nat) : CheckM TypedTerm := do
  if len = 0 then throw .emptyArray
  let idx ← fieldTerm <$> checkNoEscape idx .field
  let ioRead := .ioRead idx len
  pure ⟨.array .field len, ioRead, false⟩

partial def inferIoWrite (data ret : Term) : CheckM TypedTerm := do
  let (dataTyp, dataInner) ← inferNoEscape data
  match ← walkTyp dataTyp with
  | .array dataEltTyp _ =>
    unless ← unifyTyp dataEltTyp .field do throw $ .typeMismatch .field dataEltTyp
    let ret ← inferTerm ret
    let ioWrite := .ioWrite ⟨dataTyp, dataInner, false⟩ ret
    pure ⟨ret.typ, ioWrite, ret.escapes⟩
  | typ' => throw $ .notAnArray typ'

partial def inferVariable (x : Local) : CheckM TypedTerm := do
  let ctx ← read
  match (ctx.varTypes[x]?, x) with
  | (some t, _) => pure ⟨t, .var x, false⟩
  | (none, Local.str localName) =>
    let (typ, _) ← refLookup (Global.init localName)
    pure ⟨typ, .var x, false⟩
  | (none, _) => throw $ .unboundLocal x

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

partial def checkArgsAndInputs (func : Global) (args : List Term) (inputs : List Typ) :
    CheckM (List TypedTerm) := do
  let lenArgs := args.length
  let lenInputs := inputs.length
  unless lenArgs == lenInputs do throw $ .wrongNumArgs func lenArgs lenInputs
  let pass := fun (arg, input) => do
    let inner ← checkNoEscape arg input
    pure ⟨input, inner, false⟩
  args.zip inputs |>.mapM pass

partial def inferGlobalApplication (func : Global) (args : List Term) (u : Bool) :
    CheckM TypedTerm := do
  let ctx ← read
  match ctx.decls.getByKey func with
  | some (.function function) =>
    if function.params.isEmpty then
      let args ← checkArgsAndInputs func args (function.inputs.map Prod.snd)
      pure ⟨function.output, .app func #[] args u, false⟩
    else
      let (mvars, subst) ← instantiateParams function.params
      let inputTypes := function.inputs.map (Typ.instantiate subst ∘ Prod.snd)
      let output := Typ.instantiate subst function.output
      let args ← checkArgsAndInputs func args inputTypes
      pure ⟨output, .app func mvars args u, false⟩
  | some (.constructor dataType constr) =>
    if u then throw $ .unconstrainedConstructor func
    if dataType.params.isEmpty then
      let args ← checkArgsAndInputs func args constr.argTypes
      pure ⟨.ref dataType.name, .app func #[] args u, false⟩
    else
      let (mvars, subst) ← instantiateParams dataType.params
      let argTypes := constr.argTypes.map (Typ.instantiate subst)
      let args ← checkArgsAndInputs func args argTypes
      pure ⟨.app dataType.name mvars, .app func mvars args u, false⟩
  | _ => throw $ .cannotApply func

partial def inferLocalApplication (func : Global) (unqualifiedFunc : String)
    (args : List Term) (u : Bool) : CheckM TypedTerm := do
  let ctx ← read
  match ctx.varTypes[Local.str unqualifiedFunc]? with
  | some (.function inputs output) => do
    let args ← checkArgsAndInputs func args inputs
    pure ⟨output, .app func #[] args u, false⟩
  | some _ => throw $ .notAFunction func
  | none => inferGlobalApplication func args u

partial def inferApplication (func : Global) (args : List Term) (u : Bool) : CheckM TypedTerm :=
  match func.toName with
  | .str .anonymous unqualifiedFunc => inferLocalApplication func unqualifiedFunc args u
  | _ => inferGlobalApplication func args u

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
          unless ← unifyTyp matchTyp typedBranch.typ do
            throw $ .branchMismatch matchTyp typedBranch.typ
          pure (typedBranches, currentTypOpt))

partial def checkPattern (pat : Pattern) (typ : Typ) : CheckM $ List (Local × Typ) := do
  let binds ← aux pat typ
  let locals := binds.map Prod.fst
  unless (locals == locals.eraseDups) do throw $ .duplicatedBind pat
  pure binds
where
  aux pat typ := do
    let typ ← walkTyp typ
    match (pat, typ) with
    | (.var var, _) => pure [(var, typ)]
    | (.wildcard, _) => pure []
    | (.field _, .field) => pure []
    | (.tuple pats, .tuple typs) => do
      unless pats.size == typs.size do throw $ .incompatiblePattern pat typ
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
    | (.array pats, .array innerTyp n) => do
      unless pats.size == n do throw $ .incompatiblePattern pat typ
      pats.foldlM (init := []) fun acc pat => acc.append <$> aux pat innerTyp
    | (.ref funcName [], typ@(.function ..)) => do
      let ctx ← read
      let some (.function function) := ctx.decls.getByKey funcName
        | throw $ .incompatiblePattern pat typ
      let typ' := .function (function.inputs.map Prod.snd) function.output
      unless ← unifyTyp typ typ' do throw $ .typeMismatch typ typ'
      pure []
    | (.ref constrRef pats, .ref dataTypeRef) => do
      let ctx ← read
      let some (.dataType dataType) := ctx.decls.getByKey dataTypeRef | unreachable!
      let some (.constructor dataType' constr) := ctx.decls.getByKey constrRef
        | throw $ .notAConstructor constrRef
      unless dataType == dataType' do throw $ .incompatiblePattern pat typ
      let typs := constr.argTypes
      unless pats.length == typs.length do throw $ .wrongNumArgs constrRef pats.length typs.length
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
    | (.ref constrRef pats, .app dataTypeRef args) => do
      let ctx ← read
      let some (.dataType dataType) := ctx.decls.getByKey dataTypeRef | unreachable!
      let some (.constructor dataType' constr) := ctx.decls.getByKey constrRef
        | throw $ .notAConstructor constrRef
      unless dataType == dataType' do throw $ .incompatiblePattern pat typ
      let subst := mkParamSubst dataType.params args
      let typs := constr.argTypes.map (Typ.instantiate subst)
      unless pats.length == typs.length do throw $ .wrongNumArgs constrRef pats.length typs.length
      pats.zip typs |>.foldlM (init := []) fun acc (pat, typ) => acc.append <$> aux pat typ
    | (.or pat pat', _) => do
      let bind ← aux pat typ
      let bind' ← aux pat' typ
      if bind != bind' then throw $ .differentBindings bind bind' else pure bind
    | (.pointer pat, .pointer typ) => aux pat typ
    | _ => throw $ .incompatiblePattern pat typ

partial def inferTuple (term : Term) : CheckM (Array Typ × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  match ← walkTyp typ with
  | .tuple typs => pure (typs, inner)
  | typ' => throw $ .notATuple typ'

partial def inferArray (term : Term) : CheckM (Typ × Nat × TypedTermInner) := do
  let (typ, inner) ← inferNoEscape term
  match ← walkTyp typ with
  | .array typ n => pure (typ, n, inner)
  | typ' => throw $ .notAnArray typ'
end

/-! ## Zonking: apply substitution through the TypedTerm tree -/

mutual
partial def zonkTypedTerm (t : TypedTerm) : CheckM TypedTerm := do
  pure ⟨← zonkTyp t.typ, ← zonkInner t.inner, t.escapes⟩

partial def zonkInner : TypedTermInner → CheckM TypedTermInner
  | .unit => pure .unit
  | .var x => pure (.var x)
  | .ref g tArgs => do pure (.ref g (← tArgs.mapM zonkTyp))
  | .data d => .data <$> zonkData d
  | .ret t => .ret <$> zonkTypedTerm t
  | .let pat v b => do pure $ .let pat (← zonkTypedTerm v) (← zonkTypedTerm b)
  | .match t bs => do
    pure $ .match (← zonkTypedTerm t)
      (← bs.mapM fun (p, b) => return (p, ← zonkTypedTerm b))
  | .app g tArgs args u => do
    pure $ .app g (← tArgs.mapM zonkTyp) (← args.mapM zonkTypedTerm) u
  | .add a b => do pure $ .add (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .sub a b => do pure $ .sub (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .mul a b => do pure $ .mul (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .eqZero a => do pure $ .eqZero (← zonkTypedTerm a)
  | .proj a n => do pure $ .proj (← zonkTypedTerm a) n
  | .get a n => do pure $ .get (← zonkTypedTerm a) n
  | .slice a i j => do pure $ .slice (← zonkTypedTerm a) i j
  | .set a n v => do pure $ .set (← zonkTypedTerm a) n (← zonkTypedTerm v)
  | .store a => do pure $ .store (← zonkTypedTerm a)
  | .load a => do pure $ .load (← zonkTypedTerm a)
  | .ptrVal a => do pure $ .ptrVal (← zonkTypedTerm a)
  | .assertEq a b r => do
    pure $ .assertEq (← zonkTypedTerm a) (← zonkTypedTerm b) (← zonkTypedTerm r)
  | .ioGetInfo k => do pure $ .ioGetInfo (← zonkTypedTerm k)
  | .ioSetInfo k i l r => do
    pure $ .ioSetInfo (← zonkTypedTerm k) (← zonkTypedTerm i)
      (← zonkTypedTerm l) (← zonkTypedTerm r)
  | .ioRead i n => do pure $ .ioRead (← zonkTypedTerm i) n
  | .ioWrite d r => do pure $ .ioWrite (← zonkTypedTerm d) (← zonkTypedTerm r)
  | .u8BitDecomposition a => do pure $ .u8BitDecomposition (← zonkTypedTerm a)
  | .u8ShiftLeft a => do pure $ .u8ShiftLeft (← zonkTypedTerm a)
  | .u8ShiftRight a => do pure $ .u8ShiftRight (← zonkTypedTerm a)
  | .u8Xor a b => do pure $ .u8Xor (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u8Add a b => do pure $ .u8Add (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u8Sub a b => do pure $ .u8Sub (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u8And a b => do pure $ .u8And (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u8Or a b => do pure $ .u8Or (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u8LessThan a b => do pure $ .u8LessThan (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .u32LessThan a b => do pure $ .u32LessThan (← zonkTypedTerm a) (← zonkTypedTerm b)
  | .debug l t r => do
    pure $ .debug l (← t.mapM zonkTypedTerm) (← zonkTypedTerm r)

partial def zonkData : TypedData → CheckM TypedData
  | .field g => pure (.field g)
  | .tuple ts => do pure $ .tuple (← ts.mapM zonkTypedTerm)
  | .array ts => do pure $ .array (← ts.mapM zonkTypedTerm)
end

def getFunctionContext (function : Function) (decls : Decls) : CheckContext :=
  { decls
    varTypes := .ofList function.inputs
    returnType := function.output
    typeParams := function.params }

/-- Well-formedness: verify type references resolve. -/
partial def wellFormedDecls (decls : Decls) : Except CheckError Unit := do
  let mut visited := default
  for (_, decl) in decls.pairs do
    match EStateM.run (wellFormedDecl decl) visited with
    | .error e _ => throw e
    | .ok () visited' => visited := visited'
where
  checkUniqueParams (name : Global) (params : List String) :
      EStateM CheckError (Std.HashSet Global) Unit :=
    let rec go : List String → Std.HashSet String → EStateM CheckError (Std.HashSet Global) Unit
      | [], _ => pure ()
      | p :: ps, seen =>
        if seen.contains p then throw $ .duplicatedTypeParam name p
        else go ps (seen.insert p)
    go params {}
  wellFormedDecl : Declaration → EStateM CheckError (Std.HashSet Global) Unit
    | .dataType dataType => do
      let map ← get
      if !map.contains dataType.name then
        set $ map.insert dataType.name
        checkUniqueParams dataType.name dataType.params
        dataType.constructors.flatMap (·.argTypes) |>.forM (wellFormedType dataType.params)
    | .function function => do
      checkUniqueParams function.name function.params
      wellFormedType function.params function.output
      function.inputs.forM fun (_, typ) => wellFormedType function.params typ
    | .constructor .. => pure ()
  wellFormedType (params : List String) : Typ → EStateM CheckError (Std.HashSet Global) Unit
    | .tuple typs => typs.forM (wellFormedType params)
    | .pointer pointerTyp => wellFormedType params pointerTyp
    | .array t _ => wellFormedType params t
    | .ref ref =>
      if params.any (· == ref.toName.toString) then pure ()
      else match decls.getByKey ref with
      | some (.dataType dt) =>
        unless dt.params.isEmpty do throw $ .wrongNumTypeArgs ref 0 dt.params.length
      | some _ => throw $ .notADataType ref
      | none => throw $ .unboundGlobal ref
    | .app g args => match decls.getByKey g with
      | some (.dataType dt) => do
        unless args.size == dt.params.length do
          throw $ .wrongNumTypeArgs g args.size dt.params.length
        args.forM (wellFormedType params)
      | some _ => throw $ .notADataType g
      | none => throw $ .unboundGlobal g
    | _ => pure ()

/-- Check a function, zonking the resulting TypedTerm. -/
def checkFunction (function : Function) : CheckM TypedFunction := do
  let body ← inferTerm function.body
  unless body.escapes do
    unless ← unifyTyp body.typ function.output do
      throw $ .typeMismatch body.typ function.output
  let body ← zonkTypedTerm body
  pure ⟨function.name, function.params, function.inputs, function.output, body, function.entry⟩

end Aiur

end
