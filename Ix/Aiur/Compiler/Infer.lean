module
public import Ix.Aiur.Term

/-!
Type inference for Aiur templates.

Resolves missing type parameters at template call sites and in template patterns
using first-order unification. Runs after alias expansion and before
monomorphization.

Input:  `Toplevel` with alias-expanded types (may have `Term.app`/`Pattern.ref`
        targeting templates without explicit type arguments).
Output: `Toplevel` where every template reference carries fully resolved type
        arguments (`Term.templateApp`/`Pattern.templateRef`).
-/

public section

namespace Aiur

/-! ## Unification -/

structure UnifState where
  nextId : Nat := 0
  subst : Std.HashMap Nat Typ := {}
  deriving Inhabited

abbrev UnifM := StateT UnifState (Except String)

def freshUnif : UnifM Typ := do
  let s ← get
  set { s with nextId := s.nextId + 1 }
  pure (.unif s.nextId)

partial def walkTyp : Typ → UnifM Typ
  | .unif id => do match (← get).subst[id]? with
    | some t => walkTyp t
    | none => pure (.unif id)
  | t => pure t

partial def occursIn (id : Nat) : Typ → UnifM Bool
  | .unif id' => pure (id == id')
  | .tuple ts => ts.anyM (occursIn id)
  | .array t _ => occursIn id t
  | .pointer t => occursIn id t
  | .function ins out => do
    if ← ins.anyM (occursIn id) then pure true else occursIn id out
  | .templateApp _ args => args.anyM (occursIn id)
  | _ => pure false

def bindUnif (id : Nat) (t : Typ) : UnifM Unit := do
  if ← occursIn id t then throw s!"Infinite type: ?{id} occurs in {repr t}"
  modify fun s => { s with subst := s.subst.insert id t }

partial def unifyTyp (t1 t2 : Typ) : UnifM Unit := do
  let t1 ← walkTyp t1
  let t2 ← walkTyp t2
  match t1, t2 with
  | .unif a, .unif b => if a != b then bindUnif a t2
  | .unif a, _ => bindUnif a t2
  | _, .unif b => bindUnif b t1
  | .unit, .unit | .field, .field => pure ()
  | .tuple ts1, .tuple ts2 =>
    if ts1.size != ts2.size then throw s!"Tuple size mismatch: {ts1.size} vs {ts2.size}"
    for i in [:ts1.size] do unifyTyp ts1[i]! ts2[i]!
  | .array t1' n1, .array t2' n2 =>
    if n1 != n2 then throw s!"Array size mismatch: {n1} vs {n2}"
    unifyTyp t1' t2'
  | .pointer t1', .pointer t2' => unifyTyp t1' t2'
  | .typeRef g1, .typeRef g2 =>
    unless g1 == g2 do throw s!"Type mismatch: {g1} vs {g2}"
  | .function ins1 out1, .function ins2 out2 =>
    if ins1.length != ins2.length then throw s!"Function arity mismatch"
    for (i1, i2) in ins1.zip ins2 do unifyTyp i1 i2
    unifyTyp out1 out2
  | .typeVar s1, .typeVar s2 =>
    unless s1 == s2 do throw s!"Type variable mismatch: {s1} vs {s2}"
  | .templateApp g1 a1, .templateApp g2 a2 =>
    unless g1 == g2 do throw s!"Template mismatch: {g1} vs {g2}"
    if a1.size != a2.size then throw s!"Template arg count mismatch"
    for i in [:a1.size] do unifyTyp a1[i]! a2[i]!
  | _, _ => throw s!"Type mismatch: {repr t1} vs {repr t2}"

partial def zonkTyp : Typ → UnifM Typ
  | .unif id => do match (← get).subst[id]? with
    | some t => zonkTyp t
    | none => pure (.unif id)
  | .tuple ts => .tuple <$> ts.mapM zonkTyp
  | .array t n => return .array (← zonkTyp t) n
  | .pointer t => .pointer <$> zonkTyp t
  | .function ins out => return .function (← ins.mapM zonkTyp) (← zonkTyp out)
  | .templateApp g args => .templateApp g <$> args.mapM zonkTyp
  | t => pure t

/-! ## Symbol Table -/

inductive SymEntry where
  | function : Function → SymEntry
  | dataType : DataType → SymEntry
  | constructor : DataType → Constructor → SymEntry
  | fnTemplate : FunctionTemplate → SymEntry
  | dtTemplate : DataTypeTemplate → SymEntry
  | tmplCtor : DataTypeTemplate → Constructor → SymEntry

abbrev SymTable := Std.HashMap Global SymEntry

def buildSymTable (t : Toplevel) : SymTable := Id.run do
  let mut e : SymTable := {}
  for f in t.functions do e := e.insert f.name (.function f)
  for dt in t.dataTypes do
    e := e.insert dt.name (.dataType dt)
    for ctor in dt.constructors do
      e := e.insert (dt.name.pushNamespace ctor.nameHead) (.constructor dt ctor)
  for ft in t.functionTemplates do e := e.insert ft.name (.fnTemplate ft)
  for dtt in t.dataTypeTemplates do
    e := e.insert dtt.name (.dtTemplate dtt)
    for ctor in dtt.constructors do
      e := e.insert (dtt.name.pushNamespace ctor.nameHead) (.tmplCtor dtt ctor)
  e

/-! ## Type variable substitution (for template instantiation) -/

private partial def substTV (s : Array (String × Typ)) : Typ → Typ
  | .typeVar v => match s.find? (·.1 == v) with | some (_, t) => t | none => .typeVar v
  | .templateApp g args => .templateApp g (args.map (substTV s))
  | .tuple ts => .tuple (ts.map (substTV s))
  | .array t n => .array (substTV s t) n
  | .pointer t => .pointer (substTV s t)
  | .function ins out => .function (ins.map (substTV s)) (substTV s out)
  | t => t

/-! ## Inference context and monad -/

structure InferCtx where
  sym : SymTable
  varTypes : Std.HashMap Local Typ := {}
  returnType : Typ := .unit
  deriving Inhabited

abbrev InferM := ReaderT InferCtx UnifM

private def instantiate (typeParams : Array String) :
    InferM (Array Typ × Array (String × Typ)) := do
  let mut tyArgs := Array.mkEmpty typeParams.size
  let mut subst := Array.mkEmpty typeParams.size
  for p in typeParams do
    let v ← freshUnif
    tyArgs := tyArgs.push v
    subst := subst.push (p, v)
  pure (tyArgs, subst)

private def checkArgs (name : Global) (args : List Term) (inputTypes : List Typ)
    (infer : Term → InferM (Typ × Term)) : InferM (List Term) := do
  unless args.length == inputTypes.length do
    throw s!"{name}: expected {inputTypes.length} args, got {args.length}"
  (args.zip inputTypes).mapM fun (arg, expected) => do
    let (actual, arg') ← infer arg
    unifyTyp actual expected
    pure arg'

/-! ## Core inference -/

namespace Infer

mutual

partial def term (t : Term) : InferM (Typ × Term) := match t with
  | .unit => pure (.unit, .unit)
  | .var x => do
    let ctx ← read
    match ctx.varTypes[x]? with
    | some typ => pure (typ, .var x)
    | none =>
      let .str localName := x | throw s!"Unbound variable"
      ref (Global.init localName)
  | .ref g => ref g
  | .data d => data d
  | .ret t => do
    let ctx ← read
    let (_, t') ← check t ctx.returnType
    pure (ctx.returnType, .ret t')
  | .let pat val body => do
    let (valTyp, val') ← term val
    let (binds, pat') ← inferPat pat valTyp
    let (bodyTyp, body') ← withReader
      (fun c => { c with varTypes := c.varTypes.insertMany binds })
      (term body)
    pure (bodyTyp, .let pat' val' body')
  | .match scrut branches => do
    let (scrutTyp, scrut') ← term scrut
    let mut resultTyp : Option Typ := none
    let mut branches' : List (Pattern × Term) := []
    for (pat, body) in branches do
      let (binds, pat') ← inferPat pat scrutTyp
      let (bodyTyp, body') ← withReader
        (fun c => { c with varTypes := c.varTypes.insertMany binds })
        (term body)
      match resultTyp with
      | none => resultTyp := some bodyTyp
      | some rt => unifyTyp bodyTyp rt
      branches' := branches' ++ [(pat', body')]
    match resultTyp with
    | some typ => pure (typ, .match scrut' branches')
    | none => throw "empty match"
  | .app g args u => app g args u
  | .templateApp g tyArgs ctorOpt args u => templateApp g tyArgs ctorOpt args u
  | .ann typ t => do
    let (_, t') ← check t typ
    pure (typ, .ann typ t')
  | .add a b => binop a b .add
  | .sub a b => binop a b .sub
  | .mul a b => binop a b .mul
  | .eqZero a => do let (_, a') ← check a .field; pure (.field, .eqZero a')
  | .proj t i => do
    let (typ, t') ← term t
    let typ ← zonkTyp typ
    match typ with
    | .tuple ts =>
      if h : i < ts.size then pure (ts[i], .proj t' i)
      else throw s!"Index {i} out of bounds for tuple of size {ts.size}"
    | _ => throw s!"Expected tuple, got {repr typ}"
  | .get t i => do
    let (typ, t') ← term t
    let typ ← zonkTyp typ
    match typ with
    | .array et n =>
      if i < n then pure (et, .get t' i) else throw s!"Index {i} out of bounds"
    | _ => throw s!"Expected array, got {repr typ}"
  | .slice t i j => do
    if j < i then throw s!"Negative range {i}..{j}"
    let (typ, t') ← term t
    let typ ← zonkTyp typ
    match typ with
    | .array et n =>
      if j ≤ n then pure (.array et (j - i), .slice t' i j)
      else throw s!"Range out of bounds"
    | _ => throw s!"Expected array, got {repr typ}"
  | .set t i v => do
    let (typ, t') ← term t
    let typ ← zonkTyp typ
    match typ with
    | .array et n =>
      if i < n then do
        let (_, v') ← check v et
        pure (.array et n, .set t' i v')
      else throw s!"Index {i} out of bounds"
    | _ => throw s!"Expected array, got {repr typ}"
  | .store t => do let (typ, t') ← term t; pure (.pointer typ, .store t')
  | .load t => do
    let (typ, t') ← term t
    let inner ← freshUnif
    unifyTyp typ (.pointer inner)
    pure (← zonkTyp inner, .load t')
  | .ptrVal t => do
    let (typ, t') ← term t
    let inner ← freshUnif
    unifyTyp typ (.pointer inner)
    pure (.field, .ptrVal t')
  | .assertEq a b ret => do
    let (at', a') ← term a
    let (_, b') ← check b at'
    let (rt, ret') ← term ret
    pure (rt, .assertEq a' b' ret')
  | .ioGetInfo key => do
    let (_, key') ← term key
    pure (.tuple #[.field, .field], .ioGetInfo key')
  | .ioSetInfo key idx len ret => do
    let (_, key') ← term key
    let (_, idx') ← check idx .field
    let (_, len') ← check len .field
    let (rt, ret') ← term ret
    pure (rt, .ioSetInfo key' idx' len' ret')
  | .ioRead idx len => do
    let (_, idx') ← check idx .field
    pure (.array .field len, .ioRead idx' len)
  | .ioWrite data ret => do
    let (_, data') ← term data
    let (rt, ret') ← term ret
    pure (rt, .ioWrite data' ret')
  | .u8BitDecomposition a => do
    let (_, a') ← check a .field
    pure (.array .field 8, .u8BitDecomposition a')
  | .u8ShiftLeft a => unop a .u8ShiftLeft
  | .u8ShiftRight a => unop a .u8ShiftRight
  | .u8Xor a b => binop a b .u8Xor
  | .u8Add a b => do
    let (_, a') ← check a .field; let (_, b') ← check b .field
    pure (.tuple #[.field, .field], .u8Add a' b')
  | .u8Sub a b => do
    let (_, a') ← check a .field; let (_, b') ← check b .field
    pure (.tuple #[.field, .field], .u8Sub a' b')
  | .u8And a b => binop a b .u8And
  | .u8Or a b => binop a b .u8Or
  | .u8LessThan a b => binop a b .u8LessThan
  | .u32LessThan a b => binop a b .u32LessThan
  | .debug label dbgTerm ret => do
    let dbgTerm' ← dbgTerm.mapM fun t => Prod.snd <$> term t
    let (rt, ret') ← term ret
    pure (rt, .debug label dbgTerm' ret')

partial def check (t : Term) (expected : Typ) : InferM (Typ × Term) := do
  let (actual, t') ← term t
  unifyTyp actual expected
  pure (expected, t')

partial def ref (g : Global) : InferM (Typ × Term) := do
  let ctx ← read
  match ctx.sym[g]? with
  | some (.function f) => pure (.function (f.inputs.map Prod.snd) f.output, .ref g)
  | some (.constructor dt ctor) =>
    unless ctor.argTypes.isEmpty do throw s!"Constructor {g} requires arguments"
    pure (.typeRef dt.name, .ref g)
  | some (.fnTemplate ft) =>
    let (_, subst) ← instantiate ft.typeParams
    pure (.function (ft.inputs.map fun (_, t) => substTV subst t) (substTV subst ft.output), .ref g)
  | some (.tmplCtor dtt ctor) =>
    unless ctor.argTypes.isEmpty do throw s!"Constructor {g} requires arguments"
    let (tyArgs, _) ← instantiate dtt.typeParams
    pure (.templateApp dtt.name tyArgs,
          .templateApp dtt.name tyArgs (some ctor.nameHead) [] false)
  | some (.dataType _) | some (.dtTemplate _) => throw s!"{g} is not a value"
  | none => throw s!"Undefined: {g}"

partial def app (g : Global) (args : List Term) (u : Bool) : InferM (Typ × Term) := do
  let ctx ← read
  -- For unqualified names, check local variable types first
  match g.toName with
  | .str .anonymous name =>
    match ctx.varTypes[Local.str name]? with
    | some (.function inputs output) =>
      let args' ← checkArgs g args inputs term
      return (output, .app g args' u)
    | some _ => throw s!"{g} is not callable"
    | none => pure ()
  | _ => pure ()
  -- Global lookup
  match ctx.sym[g]? with
  | some (.function f) =>
    let args' ← checkArgs g args (f.inputs.map Prod.snd) term
    pure (f.output, .app g args' u)
  | some (.constructor dt ctor) =>
    let args' ← checkArgs g args ctor.argTypes term
    pure (.typeRef dt.name, .app g args' u)
  | some (.fnTemplate ft) =>
    let (tyArgs, subst) ← instantiate ft.typeParams
    let inputTypes := ft.inputs.map fun (_, t) => substTV subst t
    let outputType := substTV subst ft.output
    let args' ← checkArgs g args inputTypes term
    pure (outputType, .templateApp ft.name tyArgs none args' u)
  | some (.tmplCtor dtt ctor) =>
    let (tyArgs, subst) ← instantiate dtt.typeParams
    let argTypes := ctor.argTypes.map (substTV subst)
    let args' ← checkArgs g args argTypes term
    pure (.templateApp dtt.name tyArgs,
          .templateApp dtt.name tyArgs (some ctor.nameHead) args' u)
  | _ => throw s!"Cannot call {g}"

partial def templateApp (g : Global) (tyArgs : Array Typ) (ctorOpt : Option String)
    (args : List Term) (u : Bool) : InferM (Typ × Term) := do
  let ctx ← read
  match ctorOpt with
  | some ctorName =>
    match ctx.sym[g]? with
    | some (.dtTemplate dtt) =>
      unless tyArgs.size == dtt.typeParams.size do
        throw s!"{g}: expected {dtt.typeParams.size} type args, got {tyArgs.size}"
      let subst := dtt.typeParams.zip tyArgs
      match dtt.constructors.find? (·.nameHead == ctorName) with
      | some ctor =>
        let argTypes := ctor.argTypes.map (substTV subst)
        let args' ← checkArgs (g.pushNamespace ctorName) args argTypes term
        pure (.templateApp g tyArgs, .templateApp g tyArgs ctorOpt args' u)
      | none => throw s!"Unknown constructor {ctorName} for {g}"
    | _ => throw s!"{g} is not a datatype template"
  | none =>
    match ctx.sym[g]? with
    | some (.fnTemplate ft) =>
      unless tyArgs.size == ft.typeParams.size do
        throw s!"{g}: expected {ft.typeParams.size} type args, got {tyArgs.size}"
      let subst := ft.typeParams.zip tyArgs
      let inputTypes := ft.inputs.map fun (_, t) => substTV subst t
      let outputType := substTV subst ft.output
      let args' ← checkArgs g args inputTypes term
      pure (outputType, .templateApp g tyArgs none args' u)
    | _ => throw s!"{g} is not a function template"

partial def data (d : Data) : InferM (Typ × Term) := match d with
  | .field g => pure (.field, .data (.field g))
  | .tuple ts => do
    let mut typs := Array.mkEmpty ts.size
    let mut ts' := Array.mkEmpty ts.size
    for t in ts do
      let (typ, t') ← term t
      typs := typs.push typ; ts' := ts'.push t'
    pure (.tuple typs, .data (.tuple ts'))
  | .array ts => do
    if h : ts.size > 0 then
      let (typ, first) ← term ts[0]
      let mut ts' := (Array.mkEmpty ts.size).push first
      for t in ts[1:] do
        let (_, t') ← check t typ
        ts' := ts'.push t'
      pure (.array typ ts.size, .data (.array ts'))
    else throw "empty array"

partial def binop (a b : Term) (mk : Term → Term → Term) : InferM (Typ × Term) := do
  let (_, a') ← check a .field; let (_, b') ← check b .field
  pure (.field, mk a' b')

partial def unop (a : Term) (mk : Term → Term) : InferM (Typ × Term) := do
  let (_, a') ← check a .field; pure (.field, mk a')

partial def inferPat (pat : Pattern) (scrutTyp : Typ) :
    InferM (List (Local × Typ) × Pattern) :=
  match pat with
  | .var v => pure ([(v, scrutTyp)], pat)
  | .wildcard => pure ([], pat)
  | .field _ => do unifyTyp scrutTyp .field; pure ([], pat)
  | .tuple pats => do
    let scrutTyp ← zonkTyp scrutTyp
    match scrutTyp with
    | .tuple typs =>
      unless pats.size == typs.size do throw "Tuple pattern/type size mismatch"
      let mut binds : List (Local × Typ) := []
      let mut pats' := Array.mkEmpty pats.size
      for i in [:pats.size] do
        let (bs, p') ← inferPat pats[i]! typs[i]!
        binds := binds ++ bs; pats' := pats'.push p'
      pure (binds, .tuple pats')
    | _ => throw s!"Expected tuple for tuple pattern, got {repr scrutTyp}"
  | .array pats => do
    let scrutTyp ← zonkTyp scrutTyp
    match scrutTyp with
    | .array et n =>
      unless pats.size == n do throw "Array pattern/type size mismatch"
      let mut binds : List (Local × Typ) := []
      let mut pats' := Array.mkEmpty pats.size
      for p in pats do
        let (bs, p') ← inferPat p et
        binds := binds ++ bs; pats' := pats'.push p'
      pure (binds, .array pats')
    | _ => throw s!"Expected array for array pattern, got {repr scrutTyp}"
  | .or p1 p2 => do
    let (b1, p1') ← inferPat p1 scrutTyp
    let (_, p2') ← inferPat p2 scrutTyp
    pure (b1, .or p1' p2')
  | .pointer p => do
    let scrutTyp ← zonkTyp scrutTyp
    match scrutTyp with
    | .pointer inner =>
      let (bs, p') ← inferPat p inner
      pure (bs, .pointer p')
    | _ => throw s!"Expected pointer for & pattern, got {repr scrutTyp}"
  | .ref g pats => do
    let ctx ← read
    match ctx.sym[g]? with
    | some (.constructor dt ctor) =>
      unifyTyp scrutTyp (.typeRef dt.name)
      unless pats.length == ctor.argTypes.length do
        throw s!"{g}: expected {ctor.argTypes.length} pattern args, got {pats.length}"
      let mut binds : List (Local × Typ) := []
      let mut pats' : List Pattern := []
      for (p, t) in pats.zip ctor.argTypes do
        let (bs, p') ← inferPat p t
        binds := binds ++ bs; pats' := pats' ++ [p']
      pure (binds, .ref g pats')
    | some (.tmplCtor dtt ctor) =>
      let (tyArgs, subst) ← instantiate dtt.typeParams
      unifyTyp scrutTyp (.templateApp dtt.name tyArgs)
      let argTypes := ctor.argTypes.map (substTV subst)
      unless pats.length == argTypes.length do
        throw s!"{g}: expected {argTypes.length} pattern args, got {pats.length}"
      let mut binds : List (Local × Typ) := []
      let mut pats' : List Pattern := []
      for (p, t) in pats.zip argTypes do
        let (bs, p') ← inferPat p t
        binds := binds ++ bs; pats' := pats' ++ [p']
      pure (binds, .templateRef dtt.name tyArgs ctor.nameHead pats')
    | some (.function f) =>
      unifyTyp scrutTyp (.function (f.inputs.map Prod.snd) f.output)
      pure ([], .ref g pats)
    | _ => throw s!"Not a constructor: {g}"
  | .templateRef g tyArgs ctorName pats => do
    let ctx ← read
    match ctx.sym[g]? with
    | some (.dtTemplate dtt) =>
      unless tyArgs.size == dtt.typeParams.size do
        throw s!"{g}: expected {dtt.typeParams.size} type args, got {tyArgs.size}"
      let subst := dtt.typeParams.zip tyArgs
      unifyTyp scrutTyp (.templateApp g tyArgs)
      match dtt.constructors.find? (·.nameHead == ctorName) with
      | some ctor =>
        let argTypes := ctor.argTypes.map (substTV subst)
        unless pats.length == argTypes.length do
          throw s!"{g}.{ctorName}: expected {argTypes.length} args, got {pats.length}"
        let mut binds : List (Local × Typ) := []
        let mut pats' : List Pattern := []
        for (p, t) in pats.zip argTypes do
          let (bs, p') ← inferPat p t
          binds := binds ++ bs; pats' := pats' ++ [p']
        pure (binds, .templateRef g tyArgs ctorName pats')
      | none => throw s!"Unknown constructor {ctorName} for {g}"
    | _ => throw s!"{g} is not a datatype template"

end -- mutual

end Infer

/-! ## Zonk: apply substitution to terms and patterns -/

mutual
partial def zonkTerm : Term → UnifM Term
  | .templateApp g tyArgs co args u => do
    return .templateApp g (← tyArgs.mapM zonkTyp) co (← args.mapM zonkTerm) u
  | .ann typ t => return .ann (← zonkTyp typ) (← zonkTerm t)
  | .let p v b => return .let (← zonkPat p) (← zonkTerm v) (← zonkTerm b)
  | .match t bs => do
    return .match (← zonkTerm t)
      (← bs.mapM fun (p, b) => return (← zonkPat p, ← zonkTerm b))
  | .app g args u => return .app g (← args.mapM zonkTerm) u
  | .ret t => return .ret (← zonkTerm t)
  | .add a b => return .add (← zonkTerm a) (← zonkTerm b)
  | .sub a b => return .sub (← zonkTerm a) (← zonkTerm b)
  | .mul a b => return .mul (← zonkTerm a) (← zonkTerm b)
  | .eqZero a => return .eqZero (← zonkTerm a)
  | .proj a n => return .proj (← zonkTerm a) n
  | .get a n => return .get (← zonkTerm a) n
  | .slice a i j => return .slice (← zonkTerm a) i j
  | .set a i v => return .set (← zonkTerm a) i (← zonkTerm v)
  | .store a => return .store (← zonkTerm a)
  | .load a => return .load (← zonkTerm a)
  | .ptrVal a => return .ptrVal (← zonkTerm a)
  | .assertEq a b r => return .assertEq (← zonkTerm a) (← zonkTerm b) (← zonkTerm r)
  | .ioGetInfo k => return .ioGetInfo (← zonkTerm k)
  | .ioSetInfo k i l r => do
    return .ioSetInfo (← zonkTerm k) (← zonkTerm i) (← zonkTerm l) (← zonkTerm r)
  | .ioRead i n => return .ioRead (← zonkTerm i) n
  | .ioWrite d r => return .ioWrite (← zonkTerm d) (← zonkTerm r)
  | .u8BitDecomposition a => return .u8BitDecomposition (← zonkTerm a)
  | .u8ShiftLeft a => return .u8ShiftLeft (← zonkTerm a)
  | .u8ShiftRight a => return .u8ShiftRight (← zonkTerm a)
  | .u8Xor a b => return .u8Xor (← zonkTerm a) (← zonkTerm b)
  | .u8Add a b => return .u8Add (← zonkTerm a) (← zonkTerm b)
  | .u8Sub a b => return .u8Sub (← zonkTerm a) (← zonkTerm b)
  | .u8And a b => return .u8And (← zonkTerm a) (← zonkTerm b)
  | .u8Or a b => return .u8Or (← zonkTerm a) (← zonkTerm b)
  | .u8LessThan a b => return .u8LessThan (← zonkTerm a) (← zonkTerm b)
  | .u32LessThan a b => return .u32LessThan (← zonkTerm a) (← zonkTerm b)
  | .debug l t r => return .debug l (← t.mapM zonkTerm) (← zonkTerm r)
  | .data (.tuple ts) => return .data (.tuple (← ts.mapM zonkTerm))
  | .data (.array ts) => return .data (.array (← ts.mapM zonkTerm))
  | t => pure t

partial def zonkPat : Pattern → UnifM Pattern
  | .templateRef g tyArgs c ps => do
    return .templateRef g (← tyArgs.mapM zonkTyp) c (← ps.mapM zonkPat)
  | .ref g ps => return .ref g (← ps.mapM zonkPat)
  | .tuple ps => return .tuple (← ps.mapM zonkPat)
  | .array ps => return .array (← ps.mapM zonkPat)
  | .or a b => return .or (← zonkPat a) (← zonkPat b)
  | .pointer p => return .pointer (← zonkPat p)
  | p => pure p
end

/-! ## Entry point -/

def Toplevel.infer (toplevel : Toplevel) : Except String Toplevel := do
  if toplevel.dataTypeTemplates.isEmpty && toplevel.functionTemplates.isEmpty then
    return toplevel
  let sym := buildSymTable toplevel
  let mut functions := toplevel.functions
  for i in [:functions.size] do
    let f := functions[i]!
    let ctx : InferCtx := { sym, varTypes := .ofList f.inputs, returnType := f.output }
    let ((_, body'), state) ← ((Infer.term f.body).run ctx).run {}
    let (body'', _) ← (zonkTerm body').run state
    functions := functions.set! i { f with body := body'' }
  let mut fnTemplates := toplevel.functionTemplates
  for i in [:fnTemplates.size] do
    let ft : FunctionTemplate := fnTemplates[i]!
    let ctx : InferCtx := { sym, varTypes := .ofList ft.inputs, returnType := ft.output }
    let ((_, body'), state) ← ((Infer.term ft.body).run ctx).run {}
    let (body'', _) ← (zonkTerm body').run state
    fnTemplates := fnTemplates.set! i ({ ft with body := body'' } : FunctionTemplate)
  pure { toplevel with functions, functionTemplates := fnTemplates }

end Aiur

end
