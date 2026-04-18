module
public import Ix.Aiur.Check
public import Std.Data.HashSet
public import Std.Data.HashMap

/-!
Monomorphization: specialize every generic datatype and function into
concrete copies, keyed by the concrete type arguments that appear at use
sites. Operates on `TypedDecls` produced by `Check.lean`.
-/

public section

namespace Aiur

/-! ## Name mangling -/

partial def Typ.toFlatName : Typ → String
  | .field => "G"
  | .unit => "Unit"
  | Typ.ref g => g.toName.toString (escape := false)
  | .pointer t => "Ptr_" ++ t.toFlatName
  | .tuple ts => "Tup_" ++ "_".intercalate (ts.map Typ.toFlatName).toList
  | .array t n => t.toFlatName ++ "_" ++ toString n
  | t => toString (repr t)

partial def Typ.appendNameLimbs (g : Global) : Typ → Global
  | .field => g.pushNamespace "G"
  | .unit => g.pushNamespace "Unit"
  | Typ.ref g' =>
    let rec pushAll (g : Global) : Lean.Name → Global
      | .str parent s => (pushAll g parent).pushNamespace s
      | _ => g
    pushAll g g'.toName
  | .pointer t => Typ.appendNameLimbs (g.pushNamespace "Ptr") t
  | .tuple ts => ts.foldl Typ.appendNameLimbs (g.pushNamespace "Tup")
  | .array t n => g.pushNamespace (toFlatName t ++ "_" ++ toString n)
  | .function .. => g.pushNamespace "Fn"
  | .app name args =>
    args.foldl Typ.appendNameLimbs (Typ.appendNameLimbs g (.ref name))
  | .mvar id => g.pushNamespace s!"?{id}"

def concretizeName (templateName : Global) (args : Array Typ) : Global :=
  args.foldl Typ.appendNameLimbs templateName

/-! ## Substitution on TypedTerm -/

/-- Substitute type variables (param-refs) in a Typ, and rewrite `Typ.app`s that
    have been specialised to their mangled `Typ.ref`. -/
partial def rewriteTyp (subst : Global → Option Typ)
    (mono : Std.HashMap (Global × Array Typ) Global) : Typ → Typ
  | .ref g => (subst g).getD (.ref g)
  | .app g args =>
    -- Try to look up with original args first (mono map keyed by original args)
    match mono[(g, args)]? with
    | some concName => .ref concName
    | none => .app g (args.map (rewriteTyp subst mono))
  | .tuple ts => .tuple (ts.map (rewriteTyp subst mono))
  | .array t n => .array (rewriteTyp subst mono t) n
  | .pointer t => .pointer (rewriteTyp subst mono t)
  | .function ins out =>
    .function (ins.map (rewriteTyp subst mono)) (rewriteTyp subst mono out)
  | t => t

mutual
partial def rewriteTypedTerm
    (decls : Decls)
    (subst : Global → Option Typ)
    (mono : Std.HashMap (Global × Array Typ) Global) (t : TypedTerm) : TypedTerm :=
  ⟨rewriteTyp subst mono t.typ, rewriteInner decls subst mono t.inner, t.escapes⟩

partial def rewriteInner
    (decls : Decls)
    (subst : Global → Option Typ)
    (mono : Std.HashMap (Global × Array Typ) Global) : TypedTermInner → TypedTermInner
  | .unit => .unit
  | .var x => .var x
  | .ref g tArgs => .ref (rewriteGlobal decls mono g tArgs) (tArgs.map (rewriteTyp subst mono))
  | .data d => .data (rewriteData decls subst mono d)
  | .ret t => .ret (rewriteTypedTerm decls subst mono t)
  | .let p v b =>
    -- v.typ still has the pre-rewrite form (Typ.app ...) we can use for patterns
    let p' := rewritePattern decls mono v.typ p
    .let p' (rewriteTypedTerm decls subst mono v) (rewriteTypedTerm decls subst mono b)
  | .match t bs =>
    let scrutTyp := t.typ
    .match (rewriteTypedTerm decls subst mono t)
      (bs.map fun (p, b) => (rewritePattern decls mono scrutTyp p, rewriteTypedTerm decls subst mono b))
  | .app g tArgs args u =>
    -- Look up using original tArgs (mono is keyed by pre-rewrite args)
    let g' := rewriteGlobal decls mono g tArgs
    .app g' #[] (args.map (rewriteTypedTerm decls subst mono)) u
  | .add a b => .add (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .sub a b => .sub (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .mul a b => .mul (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .eqZero a => .eqZero (rewriteTypedTerm decls subst mono a)
  | .proj a n => .proj (rewriteTypedTerm decls subst mono a) n
  | .get a n => .get (rewriteTypedTerm decls subst mono a) n
  | .slice a i j => .slice (rewriteTypedTerm decls subst mono a) i j
  | .set a n v =>
    .set (rewriteTypedTerm decls subst mono a) n (rewriteTypedTerm decls subst mono v)
  | .store a => .store (rewriteTypedTerm decls subst mono a)
  | .load a => .load (rewriteTypedTerm decls subst mono a)
  | .ptrVal a => .ptrVal (rewriteTypedTerm decls subst mono a)
  | .assertEq a b r =>
    .assertEq (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
      (rewriteTypedTerm decls subst mono r)
  | .assertApp g tArgs args expected r =>
    let g' := rewriteGlobal decls mono g tArgs
    .assertApp g' #[] (args.map (rewriteTypedTerm decls subst mono))
      (rewriteTypedTerm decls subst mono expected) (rewriteTypedTerm decls subst mono r)
  | .ioGetInfo k => .ioGetInfo (rewriteTypedTerm decls subst mono k)
  | .ioSetInfo k i l r =>
    .ioSetInfo (rewriteTypedTerm decls subst mono k) (rewriteTypedTerm decls subst mono i)
      (rewriteTypedTerm decls subst mono l) (rewriteTypedTerm decls subst mono r)
  | .ioRead i n => .ioRead (rewriteTypedTerm decls subst mono i) n
  | .ioWrite d r =>
    .ioWrite (rewriteTypedTerm decls subst mono d) (rewriteTypedTerm decls subst mono r)
  | .u8BitDecomposition a => .u8BitDecomposition (rewriteTypedTerm decls subst mono a)
  | .u8ShiftLeft a => .u8ShiftLeft (rewriteTypedTerm decls subst mono a)
  | .u8ShiftRight a => .u8ShiftRight (rewriteTypedTerm decls subst mono a)
  | .u8Xor a b =>
    .u8Xor (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Add a b =>
    .u8Add (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Sub a b =>
    .u8Sub (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8And a b =>
    .u8And (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8Or a b =>
    .u8Or (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u8LessThan a b =>
    .u8LessThan (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .u32LessThan a b =>
    .u32LessThan (rewriteTypedTerm decls subst mono a) (rewriteTypedTerm decls subst mono b)
  | .debug l t r =>
    .debug l (t.map (rewriteTypedTerm decls subst mono)) (rewriteTypedTerm decls subst mono r)

partial def rewriteData
    (decls : Decls)
    (subst : Global → Option Typ)
    (mono : Std.HashMap (Global × Array Typ) Global) : TypedData → TypedData
  | .field g => .field g
  | .tuple ts => .tuple (ts.map (rewriteTypedTerm decls subst mono))
  | .array ts => .array (ts.map (rewriteTypedTerm decls subst mono))

/-- Rewrite a reference to a function/constructor/datatype.
    For a constructor like `Wrapper.Mk` with tArgs `#[field]`, resolves to
    `Wrapper_G.Mk`. For a function, resolves to the concretized function name. -/
partial def rewriteGlobal
    (decls : Decls)
    (mono : Std.HashMap (Global × Array Typ) Global)
    (g : Global) (tArgs : Array Typ) : Global :=
  if tArgs.isEmpty then g  -- non-parametric, leave alone
  else match decls.getByKey g with
  | some (.function _) =>
    match mono[(g, tArgs)]? with
    | some concName => concName
    | none => g
  | some (.constructor dt _) =>
    match g.popNamespace with
    | some (ctorName, _) =>
      match mono[(dt.name, tArgs)]? with
      | some concDTName => concDTName.pushNamespace ctorName
      | none => g
    | none => g
  | _ => g

/-- Rewrite constructor names in patterns, using the expected (unrewritten) type
    to determine which monomorphic instance to use. -/
partial def rewritePattern
    (decls : Decls)
    (mono : Std.HashMap (Global × Array Typ) Global)
    (expectedTyp : Typ) (pat : Pattern) : Pattern :=
  match pat with
  | .ref g pats =>
    let tArgs : Array Typ := match expectedTyp with
      | .app _ args => args
      | _ => #[]
    let g' := rewriteGlobal decls mono g tArgs
    let pats' := match decls.getByKey g with
      | some (.constructor dt c) =>
        let subst := mkParamSubst dt.params tArgs
        let argTyps := c.argTypes.map (Typ.instantiate subst)
        pats.zip argTyps |>.map fun (p, t) => rewritePattern decls mono t p
      | _ => pats.map (rewritePattern decls mono .unit)
    .ref g' pats'
  | .tuple pats =>
    match expectedTyp with
    | .tuple typs =>
      if pats.size == typs.size then
        .tuple (pats.zip typs |>.map fun (p, t) => rewritePattern decls mono t p)
      else pat
    | _ => pat
  | .array pats =>
    match expectedTyp with
    | .array t _ => .array (pats.map (rewritePattern decls mono t))
    | _ => pat
  | .or a b =>
    .or (rewritePattern decls mono expectedTyp a) (rewritePattern decls mono expectedTyp b)
  | .pointer p =>
    match expectedTyp with
    | .pointer inner => .pointer (rewritePattern decls mono inner p)
    | _ => .pointer p
  | _ => pat
end

/-! ## Discovery: walk TypedDecls collecting instantiations -/

/-- Collect all `Typ.app (g, args)` instantiations in a type. -/
partial def collectInTyp (seen : Std.HashSet (Global × Array Typ)) :
    Typ → Std.HashSet (Global × Array Typ)
  | .app g args =>
    let seen := args.foldl collectInTyp seen
    seen.insert (g, args)
  | .tuple ts => ts.foldl collectInTyp seen
  | .array t _ => collectInTyp seen t
  | .pointer t => collectInTyp seen t
  | .function ins out =>
    let seen := ins.foldl collectInTyp seen
    collectInTyp seen out
  | _ => seen

mutual
partial def collectInTypedTerm (seen : Std.HashSet (Global × Array Typ))
    (t : TypedTerm) : Std.HashSet (Global × Array Typ) :=
  let seen := collectInTyp seen t.typ
  collectInInner seen t.inner

partial def collectInInner (seen : Std.HashSet (Global × Array Typ)) :
    TypedTermInner → Std.HashSet (Global × Array Typ)
  | .unit | .var _ | .ref _ _ => seen
  | .data d => collectInData seen d
  | .ret t => collectInTypedTerm seen t
  | .let _ v b => collectInTypedTerm (collectInTypedTerm seen v) b
  | .match t bs =>
    let seen := collectInTypedTerm seen t
    bs.foldl (fun s (_, b) => collectInTypedTerm s b) seen
  | .app _ tArgs args _ =>
    let seen := tArgs.foldl collectInTyp seen
    let seen := args.foldl collectInTypedTerm seen
    -- We DON'T insert the call instantiation here; that's handled by the
    -- worklist against the callee's declaration. The tArgs on the .app node
    -- carry the instantiation used, which gets recorded by examining the
    -- callee's declaration.
    seen
  | .add a b | .sub a b | .mul a b | .u8Xor a b | .u8Add a b | .u8Sub a b
  | .u8And a b | .u8Or a b | .u8LessThan a b | .u32LessThan a b =>
    collectInTypedTerm (collectInTypedTerm seen a) b
  | .eqZero a | .store a | .load a | .ptrVal a | .u8BitDecomposition a
  | .u8ShiftLeft a | .u8ShiftRight a | .ioGetInfo a => collectInTypedTerm seen a
  | .proj a _ | .get a _ | .slice a _ _ => collectInTypedTerm seen a
  | .set a _ v => collectInTypedTerm (collectInTypedTerm seen a) v
  | .assertEq a b r =>
    collectInTypedTerm (collectInTypedTerm (collectInTypedTerm seen a) b) r
  | .assertApp _ tArgs args expected r =>
    let seen := tArgs.foldl collectInTyp seen
    let seen := args.foldl collectInTypedTerm seen
    collectInTypedTerm (collectInTypedTerm seen expected) r
  | .ioSetInfo k i l r =>
    collectInTypedTerm (collectInTypedTerm
      (collectInTypedTerm (collectInTypedTerm seen k) i) l) r
  | .ioRead i _ => collectInTypedTerm seen i
  | .ioWrite d r => collectInTypedTerm (collectInTypedTerm seen d) r
  | .debug _ t r =>
    let seen := match t with | some t => collectInTypedTerm seen t | none => seen
    collectInTypedTerm seen r

partial def collectInData (seen : Std.HashSet (Global × Array Typ)) :
    TypedData → Std.HashSet (Global × Array Typ)
  | .field _ => seen
  | .tuple ts | .array ts => ts.foldl collectInTypedTerm seen
end

/-- Also collect function-call instantiations via the typedterm's .app tArgs. -/
partial def collectCalls (seen : Std.HashSet (Global × Array Typ))
    (decls : Decls) (t : TypedTerm) : Std.HashSet (Global × Array Typ) :=
  collectCallsI decls t.inner seen
where
  goT seen t := collectCallsI decls t.inner seen
  collectCallsI : Decls → TypedTermInner → Std.HashSet (Global × Array Typ)
      → Std.HashSet (Global × Array Typ) :=
    fun decls i seen => match i with
    | .unit | .var _ | .ref _ _ => seen
    | .data (.field _) => seen
    | .data (.tuple ts) | .data (.array ts) => ts.foldl goT seen
    | .ret t => goT seen t
    | .let _ v b => goT (goT seen v) b
    | .match t bs => bs.foldl (fun s (_, b) => goT s b) (goT seen t)
    | .app g tArgs args _ =>
      let seen := args.foldl goT seen
      if tArgs.isEmpty then seen else
        match decls.getByKey g with
        | some (.function _) => seen.insert (g, tArgs)
        | some (.constructor dt _) => seen.insert (dt.name, tArgs)
        | _ => seen
    | .add a b | .sub a b | .mul a b | .u8Xor a b | .u8Add a b | .u8Sub a b
    | .u8And a b | .u8Or a b | .u8LessThan a b | .u32LessThan a b => goT (goT seen a) b
    | .eqZero a | .store a | .load a | .ptrVal a | .u8BitDecomposition a
    | .u8ShiftLeft a | .u8ShiftRight a | .ioGetInfo a => goT seen a
    | .proj a _ | .get a _ | .slice a _ _ => goT seen a
    | .set a _ v => goT (goT seen a) v
    | .assertEq a b r => goT (goT (goT seen a) b) r
    | .assertApp g tArgs args expected r =>
      let seen := args.foldl goT (goT (goT seen expected) r)
      if tArgs.isEmpty then seen else
        match decls.getByKey g with
        | some (.function _) => seen.insert (g, tArgs)
        | _ => seen
    | .ioSetInfo k i l r => goT (goT (goT (goT seen k) i) l) r
    | .ioRead i _ => goT seen i
    | .ioWrite d r => goT (goT seen d) r
    | .debug _ t r =>
      let seen := match t with | some t => goT seen t | none => seen
      goT seen r

/-! ## Substitution on TypedTerm (for template body specialization) -/

mutual
partial def substInTypedTerm (subst : Global → Option Typ) (t : TypedTerm) : TypedTerm :=
  ⟨Typ.instantiate subst t.typ, substInInner subst t.inner, t.escapes⟩

partial def substInInner (subst : Global → Option Typ) : TypedTermInner → TypedTermInner
  | .unit => .unit
  | .var x => .var x
  | .ref g tArgs => .ref g (tArgs.map (Typ.instantiate subst))
  | .data d => .data (substInData subst d)
  | .ret t => .ret (substInTypedTerm subst t)
  | .let p v b => .let p (substInTypedTerm subst v) (substInTypedTerm subst b)
  | .match t bs =>
    .match (substInTypedTerm subst t)
      (bs.map fun (p, b) => (p, substInTypedTerm subst b))
  | .app g tArgs args u =>
    .app g (tArgs.map (Typ.instantiate subst)) (args.map (substInTypedTerm subst)) u
  | .add a b => .add (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .sub a b => .sub (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .mul a b => .mul (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .eqZero a => .eqZero (substInTypedTerm subst a)
  | .proj a n => .proj (substInTypedTerm subst a) n
  | .get a n => .get (substInTypedTerm subst a) n
  | .slice a i j => .slice (substInTypedTerm subst a) i j
  | .set a n v => .set (substInTypedTerm subst a) n (substInTypedTerm subst v)
  | .store a => .store (substInTypedTerm subst a)
  | .load a => .load (substInTypedTerm subst a)
  | .ptrVal a => .ptrVal (substInTypedTerm subst a)
  | .assertEq a b r =>
    .assertEq (substInTypedTerm subst a) (substInTypedTerm subst b) (substInTypedTerm subst r)
  | .assertApp g tArgs args expected r =>
    .assertApp g (tArgs.map (Typ.instantiate subst))
      (args.map (substInTypedTerm subst))
      (substInTypedTerm subst expected) (substInTypedTerm subst r)
  | .ioGetInfo k => .ioGetInfo (substInTypedTerm subst k)
  | .ioSetInfo k i l r =>
    .ioSetInfo (substInTypedTerm subst k) (substInTypedTerm subst i)
      (substInTypedTerm subst l) (substInTypedTerm subst r)
  | .ioRead i n => .ioRead (substInTypedTerm subst i) n
  | .ioWrite d r => .ioWrite (substInTypedTerm subst d) (substInTypedTerm subst r)
  | .u8BitDecomposition a => .u8BitDecomposition (substInTypedTerm subst a)
  | .u8ShiftLeft a => .u8ShiftLeft (substInTypedTerm subst a)
  | .u8ShiftRight a => .u8ShiftRight (substInTypedTerm subst a)
  | .u8Xor a b => .u8Xor (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Add a b => .u8Add (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Sub a b => .u8Sub (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8And a b => .u8And (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8Or a b => .u8Or (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u8LessThan a b => .u8LessThan (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .u32LessThan a b => .u32LessThan (substInTypedTerm subst a) (substInTypedTerm subst b)
  | .debug l t r =>
    .debug l (t.map (substInTypedTerm subst)) (substInTypedTerm subst r)

partial def substInData (subst : Global → Option Typ) : TypedData → TypedData
  | .field g => .field g
  | .tuple ts => .tuple (ts.map (substInTypedTerm subst))
  | .array ts => .array (ts.map (substInTypedTerm subst))
end

/-! ## The main pass -/

def TypedDecls.concretize (decls : TypedDecls) : Except String TypedDecls := do
  -- Step 1: discover all initial instantiations from concrete declarations
  let mut pending : Std.HashSet (Global × Array Typ) := {}
  let plainDecls : Decls := decls.foldl (init := default) fun acc (name, d) =>
    match d with
    | .function f =>
      let f' : Function :=
        { name := f.name, params := f.params, inputs := f.inputs, output := f.output
          body := .unit, entry := f.entry }
      acc.insert name (.function f')
    | .dataType dt => acc.insert name (.dataType dt)
    | .constructor dt c => acc.insert name (.constructor dt c)
  for (_, d) in decls.pairs do
    match d with
    | .function f =>
      if f.params.isEmpty then
        pending := collectInTyp pending f.output
        pending := f.inputs.foldl (fun s (_, t) => collectInTyp s t) pending
        pending := collectInTypedTerm pending f.body
        pending := collectCalls pending plainDecls f.body
    | .dataType dt =>
      if dt.params.isEmpty then
        pending := dt.constructors.foldl
          (fun s c => c.argTypes.foldl collectInTyp s) pending
    | _ => pure ()

  -- Step 2: fixpoint - generate monomorphic decls
  let mut mono : Std.HashMap (Global × Array Typ) Global := {}
  let mut newFunctions : Array TypedFunction := #[]
  let mut newDataTypes : Array DataType := #[]
  let mut seen : Std.HashSet (Global × Array Typ) := {}
  while !pending.isEmpty do
    let batch := pending
    pending := {}
    for (name, args) in batch do
      if seen.contains (name, args) then continue
      seen := seen.insert (name, args)
      let concName := concretizeName name args
      mono := mono.insert (name, args) concName
      -- Look up the template
      match decls.getByKey name with
      | some (.function f) =>
        if f.params.length != args.size then
          throw s!"Template {name}: expected {f.params.length} type args, got {args.size}"
        let subst := mkParamSubst f.params args
        -- Apply substitution through the template to get monomorphic version
        let newInputs := f.inputs.map fun (l, t) => (l, Typ.instantiate subst t)
        let newOutput := Typ.instantiate subst f.output
        let newBody := substInTypedTerm subst f.body
        -- Now collect instantiations from the substituted body
        pending := collectInTyp pending newOutput
        pending := newInputs.foldl (fun s (_, t) => collectInTyp s t) pending
        pending := collectInTypedTerm pending newBody
        pending := collectCalls pending plainDecls newBody
        newFunctions := newFunctions.push
          { name := concName, params := [], inputs := newInputs
            output := newOutput, body := newBody, entry := false }
      | some (.dataType dt) =>
        if dt.params.length != args.size then
          throw s!"Template {name}: expected {dt.params.length} type args, got {args.size}"
        let subst := mkParamSubst dt.params args
        let newCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (Typ.instantiate subst) }
        -- Collect from substituted ctor arg types
        pending := newCtors.foldl
          (fun s c => c.argTypes.foldl collectInTyp s) pending
        newDataTypes := newDataTypes.push
          { name := concName, params := [], constructors := newCtors }
      | _ => throw s!"Template {name} not found in decls"

  -- Step 3: build the rewritten TypedDecls
  let mut result : TypedDecls := default
  let emptySubst : Global → Option Typ := fun _ => none
  -- Keep concrete decls, rewriting their references
  for (key, d) in decls.pairs do
    match d with
    | .function f =>
      if f.params.isEmpty then
        let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
        let newOutput := rewriteTyp emptySubst mono f.output
        let newBody := rewriteTypedTerm plainDecls emptySubst mono f.body
        result := result.insert key (.function
          { f with inputs := newInputs, output := newOutput, body := newBody })
    | .dataType dt =>
      if dt.params.isEmpty then
        let newCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        result := result.insert key (.dataType { dt with constructors := newCtors })
    | .constructor dt c =>
      if dt.params.isEmpty then
        let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
        let newCtor : Constructor := { c with argTypes := newArgTypes }
        let rewrittenCtors := dt.constructors.map fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        result := result.insert key (.constructor newDt newCtor)
  -- Add monomorphic datatypes and their constructors
  for dt in newDataTypes do
    -- Rewrite inner references in the ctor types (for nested templates)
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt := { dt with constructors := rewrittenCtors }
    result := result.insert dt.name (.dataType newDt)
    for c in rewrittenCtors do
      let cName := dt.name.pushNamespace c.nameHead
      result := result.insert cName (.constructor newDt c)
  -- Add monomorphic functions
  for f in newFunctions do
    let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
    let newOutput := rewriteTyp emptySubst mono f.output
    let newBody := rewriteTypedTerm plainDecls emptySubst mono f.body
    let newF := { f with inputs := newInputs, output := newOutput, body := newBody }
    result := result.insert f.name (.function newF)
  pure result

end Aiur

end
