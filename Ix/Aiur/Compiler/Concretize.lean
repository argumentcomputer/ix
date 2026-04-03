module
public import Ix.Aiur.Term

/-!
Template concretization: monomorphizes datatype and function templates.

Takes a `Toplevel` that may contain `DataTypeTemplate`s and `FunctionTemplate`s
and produces a `Toplevel` with only concrete definitions. Template type variables
(`Typ.typeVar`), template type applications (`Typ.templateApp`), template term
applications (`Term.templateApp`), and template pattern references
(`Pattern.templateRef`) are all eliminated.
-/

public section

namespace Aiur

/-- Substitution map from type parameter names to concrete types. -/
abbrev TypeSubst := Array (String × Typ)

/-- Compact string name for a type (used in array naming: `[G; 8]` → `"G_8"`). -/
partial def Typ.toFlatName : Typ → String
  | .field => "G"
  | .unit => "Unit"
  | .typeRef ref => ref.toName.toString (escape := false)
  | .pointer t => "Ptr_" ++ t.toFlatName
  | .tuple ts => "Tup_" ++ "_".intercalate (ts.map Typ.toFlatName).toList
  | .array t n => t.toFlatName ++ "_" ++ toString n
  | t => toString (repr t)

/-- Append name limbs for a concrete type argument to a `Global` name. -/
partial def Typ.appendNameLimbs (g : Global) : Typ → Global
  | .field => g.pushNamespace "G"
  | .unit => g.pushNamespace "Unit"
  | .typeRef ref =>
    let rec pushAll (g : Global) : Lean.Name → Global
      | .str parent s => (pushAll g parent).pushNamespace s
      | _ => g
    pushAll g ref.toName
  | .pointer t => Typ.appendNameLimbs (g.pushNamespace "Ptr") t
  | .tuple ts => ts.foldl Typ.appendNameLimbs (g.pushNamespace "Tup")
  | .array t n => g.pushNamespace (toFlatName t ++ "_" ++ toString n)
  | .function .. => g.pushNamespace "Fn"
  | .typeVar s => g.pushNamespace s
  | .templateApp name args =>
    args.foldl Typ.appendNameLimbs (Typ.appendNameLimbs g (.typeRef name))
  | .unif id => g.pushNamespace s!"?{id}"

/-- Compute the concretized name for a template with given concrete type arguments. -/
def concretizeName (templateName : Global) (args : Array Typ) : Global :=
  args.foldl Typ.appendNameLimbs templateName

/-- Monad for concretization: tracks discovered template instantiations. -/
-- Each entry: (templateName, typeArgs, isDataType)
abbrev ConcM := StateT (Array (Global × Array Typ × Bool)) (Except String)

/-- Record a template instantiation to process. -/
def recordInstantiation (name : Global) (args : Array Typ) (isDT : Bool) : ConcM Unit :=
  modify fun wl => wl.push (name, args, isDT)

/-- Resolve all template references in a `Typ` to concrete types.
    Collects newly discovered instantiations in the state. -/
partial def Typ.resolve
    (dtTemplates : Std.HashMap Global DataTypeTemplate)
    (fnTemplates : Std.HashMap Global FunctionTemplate) : Typ → ConcM Typ
  | .templateApp name args => do
    let args ← args.mapM (Typ.resolve dtTemplates fnTemplates)
    if dtTemplates.contains name then
      recordInstantiation name args true
      pure $ .typeRef (concretizeName name args)
    else
      throw s!"Unknown template `{name}`"
  | .typeVar s => throw s!"Unresolved type variable `{s}`"
  | .tuple ts => do pure $ .tuple (← ts.mapM (Typ.resolve dtTemplates fnTemplates))
  | .array t n => do pure $ .array (← Typ.resolve dtTemplates fnTemplates t) n
  | .pointer t => do pure $ .pointer (← Typ.resolve dtTemplates fnTemplates t)
  | .function ins out => do
    pure $ .function (← ins.mapM (Typ.resolve dtTemplates fnTemplates))
      (← Typ.resolve dtTemplates fnTemplates out)
  | t => pure t

mutual

/-- Resolve all template references in a `Term` to concrete references. -/
partial def Term.resolve
    (dtTemplates : Std.HashMap Global DataTypeTemplate)
    (fnTemplates : Std.HashMap Global FunctionTemplate) : Term → ConcM Term
  | .templateApp name tyArgs ctorOpt args unconstrained => do
    let tyArgs ← tyArgs.mapM (Typ.resolve dtTemplates fnTemplates)
    let args ← args.mapM (Term.resolve dtTemplates fnTemplates)
    match ctorOpt with
    | some ctor =>
      recordInstantiation name tyArgs true
      let concName := (concretizeName name tyArgs).pushNamespace ctor
      pure $ .app concName args unconstrained
    | none =>
      if fnTemplates.contains name then
        recordInstantiation name tyArgs false
        pure $ .app (concretizeName name tyArgs) args unconstrained
      else
        throw s!"Unknown template `{name}`"
  | .ann t term => do
    pure $ .ann (← Typ.resolve dtTemplates fnTemplates t)
      (← Term.resolve dtTemplates fnTemplates term)
  | .let pat val body => do
    pure $ .let (← Pattern.resolve dtTemplates fnTemplates pat)
      (← Term.resolve dtTemplates fnTemplates val)
      (← Term.resolve dtTemplates fnTemplates body)
  | .match term branches => do
    let term ← Term.resolve dtTemplates fnTemplates term
    let branches ← branches.mapM fun (pat, t) => do
      pure (← Pattern.resolve dtTemplates fnTemplates pat,
            ← Term.resolve dtTemplates fnTemplates t)
    pure $ .match term branches
  | .app g args unconstrained => do
    pure $ .app g (← args.mapM (Term.resolve dtTemplates fnTemplates)) unconstrained
  | .ret t => do pure $ .ret (← Term.resolve dtTemplates fnTemplates t)
  | .add a b => do
    pure $ .add (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .sub a b => do
    pure $ .sub (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .mul a b => do
    pure $ .mul (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .eqZero a => do pure $ .eqZero (← Term.resolve dtTemplates fnTemplates a)
  | .proj a n => do pure $ .proj (← Term.resolve dtTemplates fnTemplates a) n
  | .get a n => do pure $ .get (← Term.resolve dtTemplates fnTemplates a) n
  | .slice a i j => do pure $ .slice (← Term.resolve dtTemplates fnTemplates a) i j
  | .set a i v => do
    pure $ .set (← Term.resolve dtTemplates fnTemplates a) i
      (← Term.resolve dtTemplates fnTemplates v)
  | .store a => do pure $ .store (← Term.resolve dtTemplates fnTemplates a)
  | .load a => do pure $ .load (← Term.resolve dtTemplates fnTemplates a)
  | .ptrVal a => do pure $ .ptrVal (← Term.resolve dtTemplates fnTemplates a)
  | .assertEq a b ret => do
    pure $ .assertEq (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
      (← Term.resolve dtTemplates fnTemplates ret)
  | .ioGetInfo key => do pure $ .ioGetInfo (← Term.resolve dtTemplates fnTemplates key)
  | .ioSetInfo key idx len ret => do
    pure $ .ioSetInfo (← Term.resolve dtTemplates fnTemplates key)
      (← Term.resolve dtTemplates fnTemplates idx)
      (← Term.resolve dtTemplates fnTemplates len)
      (← Term.resolve dtTemplates fnTemplates ret)
  | .ioRead idx len => do
    pure $ .ioRead (← Term.resolve dtTemplates fnTemplates idx) len
  | .ioWrite data ret => do
    pure $ .ioWrite (← Term.resolve dtTemplates fnTemplates data)
      (← Term.resolve dtTemplates fnTemplates ret)
  | .debug label term ret => do
    pure $ .debug label (← term.mapM (Term.resolve dtTemplates fnTemplates))
      (← Term.resolve dtTemplates fnTemplates ret)
  | .data (.tuple ts) => do
    pure $ .data (.tuple (← ts.mapM (Term.resolve dtTemplates fnTemplates)))
  | .data (.array ts) => do
    pure $ .data (.array (← ts.mapM (Term.resolve dtTemplates fnTemplates)))
  | .u8BitDecomposition a => do
    pure $ .u8BitDecomposition (← Term.resolve dtTemplates fnTemplates a)
  | .u8ShiftLeft a => do
    pure $ .u8ShiftLeft (← Term.resolve dtTemplates fnTemplates a)
  | .u8ShiftRight a => do
    pure $ .u8ShiftRight (← Term.resolve dtTemplates fnTemplates a)
  | .u8Xor a b => do
    pure $ .u8Xor (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u8Add a b => do
    pure $ .u8Add (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u8Sub a b => do
    pure $ .u8Sub (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u8And a b => do
    pure $ .u8And (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u8Or a b => do
    pure $ .u8Or (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u8LessThan a b => do
    pure $ .u8LessThan (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | .u32LessThan a b => do
    pure $ .u32LessThan (← Term.resolve dtTemplates fnTemplates a)
      (← Term.resolve dtTemplates fnTemplates b)
  | t => pure t

/-- Resolve all template references in a `Pattern`. -/
partial def Pattern.resolve
    (dtTemplates : Std.HashMap Global DataTypeTemplate)
    (fnTemplates : Std.HashMap Global FunctionTemplate) : Pattern → ConcM Pattern
  | .templateRef name tyArgs ctor pats => do
    let tyArgs ← tyArgs.mapM (Typ.resolve dtTemplates fnTemplates)
    let pats ← pats.mapM (Pattern.resolve dtTemplates fnTemplates)
    recordInstantiation name tyArgs true
    pure $ .ref ((concretizeName name tyArgs).pushNamespace ctor) pats
  | .ref g pats => do
    pure $ .ref g (← pats.mapM (Pattern.resolve dtTemplates fnTemplates))
  | .tuple pats => do
    pure $ .tuple (← pats.mapM (Pattern.resolve dtTemplates fnTemplates))
  | .array pats => do
    pure $ .array (← pats.mapM (Pattern.resolve dtTemplates fnTemplates))
  | .or a b => do
    pure $ .or (← Pattern.resolve dtTemplates fnTemplates a)
      (← Pattern.resolve dtTemplates fnTemplates b)
  | .pointer p => do
    pure $ .pointer (← Pattern.resolve dtTemplates fnTemplates p)
  | p => pure p

end

partial def Typ.substitute (subst : TypeSubst) : Typ → Typ
  | .typeVar s => match subst.find? (·.1 == s) with
    | some (_, t) => t
    | none => .typeVar s
  | .templateApp name args => .templateApp name (args.map (Typ.substitute subst))
  | .tuple ts => .tuple (ts.map (Typ.substitute subst))
  | .array t n => .array (Typ.substitute subst t) n
  | .pointer t => .pointer (Typ.substitute subst t)
  | .function ins out => .function (ins.map (Typ.substitute subst)) (Typ.substitute subst out)
  | t => t

mutual
partial def Term.substitute (subst : TypeSubst) : Term → Term
  | .ann t term => .ann (Typ.substitute subst t) (Term.substitute subst term)
  | .let pat val body =>
    .let (Pattern.substitute subst pat) (Term.substitute subst val)
      (Term.substitute subst body)
  | .match term branches =>
    .match (Term.substitute subst term)
      (branches.map fun (pat, t) => (Pattern.substitute subst pat, Term.substitute subst t))
  | .app g args uc => .app g (args.map (Term.substitute subst)) uc
  | .ret t => .ret (Term.substitute subst t)
  | .add a b => .add (Term.substitute subst a) (Term.substitute subst b)
  | .sub a b => .sub (Term.substitute subst a) (Term.substitute subst b)
  | .mul a b => .mul (Term.substitute subst a) (Term.substitute subst b)
  | .eqZero a => .eqZero (Term.substitute subst a)
  | .proj a n => .proj (Term.substitute subst a) n
  | .get a n => .get (Term.substitute subst a) n
  | .slice a i j => .slice (Term.substitute subst a) i j
  | .set a i v => .set (Term.substitute subst a) i (Term.substitute subst v)
  | .store a => .store (Term.substitute subst a)
  | .load a => .load (Term.substitute subst a)
  | .ptrVal a => .ptrVal (Term.substitute subst a)
  | .assertEq a b ret =>
    .assertEq (Term.substitute subst a) (Term.substitute subst b) (Term.substitute subst ret)
  | .ioGetInfo key => .ioGetInfo (Term.substitute subst key)
  | .ioSetInfo key idx len ret =>
    .ioSetInfo (Term.substitute subst key) (Term.substitute subst idx)
      (Term.substitute subst len) (Term.substitute subst ret)
  | .ioRead idx len => .ioRead (Term.substitute subst idx) len
  | .ioWrite data ret => .ioWrite (Term.substitute subst data) (Term.substitute subst ret)
  | .u8BitDecomposition a => .u8BitDecomposition (Term.substitute subst a)
  | .u8ShiftLeft a => .u8ShiftLeft (Term.substitute subst a)
  | .u8ShiftRight a => .u8ShiftRight (Term.substitute subst a)
  | .u8Xor a b => .u8Xor (Term.substitute subst a) (Term.substitute subst b)
  | .u8Add a b => .u8Add (Term.substitute subst a) (Term.substitute subst b)
  | .u8Sub a b => .u8Sub (Term.substitute subst a) (Term.substitute subst b)
  | .u8And a b => .u8And (Term.substitute subst a) (Term.substitute subst b)
  | .u8Or a b => .u8Or (Term.substitute subst a) (Term.substitute subst b)
  | .u8LessThan a b => .u8LessThan (Term.substitute subst a) (Term.substitute subst b)
  | .u32LessThan a b => .u32LessThan (Term.substitute subst a) (Term.substitute subst b)
  | .debug label term ret =>
    .debug label (term.map (Term.substitute subst)) (Term.substitute subst ret)
  | .data (.tuple ts) => .data (.tuple (ts.map (Term.substitute subst)))
  | .data (.array ts) => .data (.array (ts.map (Term.substitute subst)))
  | .templateApp name tyArgs ctorOpt args uc =>
    .templateApp name (tyArgs.map (Typ.substitute subst)) ctorOpt
      (args.map (Term.substitute subst)) uc
  | t => t
partial def Pattern.substitute (subst : TypeSubst) : Pattern → Pattern
  | .templateRef name tyArgs ctor pats =>
    .templateRef name (tyArgs.map (Typ.substitute subst)) ctor
      (pats.map (Pattern.substitute subst))
  | .ref g pats => .ref g (pats.map (Pattern.substitute subst))
  | .tuple pats => .tuple (pats.map (Pattern.substitute subst))
  | .array pats => .array (pats.map (Pattern.substitute subst))
  | .or a b => .or (Pattern.substitute subst a) (Pattern.substitute subst b)
  | .pointer p => .pointer (Pattern.substitute subst p)
  | p => p
end

/-- Apply substitution then resolve a type. -/
def resolveTyp
    (dtTemplates : Std.HashMap Global DataTypeTemplate)
    (fnTemplates : Std.HashMap Global FunctionTemplate)
    (subst : TypeSubst) (t : Typ) : ConcM Typ :=
  Typ.resolve dtTemplates fnTemplates (Typ.substitute subst t)

/-- Apply substitution to a Term then resolve all template refs. -/
def resolveTerm
    (dtTemplates : Std.HashMap Global DataTypeTemplate)
    (fnTemplates : Std.HashMap Global FunctionTemplate)
    (subst : TypeSubst) (t : Term) : ConcM Term :=
  Term.resolve dtTemplates fnTemplates (Term.substitute subst t)

/-- Collect all `Typ.typeRef` globals from a type. -/
partial def collectTypRefs : Typ → Std.HashSet Global → Std.HashSet Global
  | .typeRef g, s => s.insert g
  | .tuple ts, s => ts.foldl (fun s t => collectTypRefs t s) s
  | .array t _, s => collectTypRefs t s
  | .pointer t, s => collectTypRefs t s
  | .function ins out, s =>
    collectTypRefs out (ins.foldl (fun s t => collectTypRefs t s) s)
  | _, s => s

/-- Collect all `Term.app` target names from a term (non-recursive into callees). -/
partial def collectCallTargets (t : Term) : Std.HashSet Global :=
  go t {}
where
  go : Term → Std.HashSet Global → Std.HashSet Global
    | .app g args _, s => args.foldl (fun s a => go a s) (s.insert g)
    | .let _ val body, s => go body (go val s)
    | .match term branches, s =>
      branches.foldl (fun s (_, t) => go t s) (go term s)
    | .ret t, s => go t s
    | .add a b, s | .sub a b, s | .mul a b, s => go b (go a s)
    | .eqZero a, s | .store a, s | .load a, s | .ptrVal a, s => go a s
    | .proj a _, s | .get a _, s | .slice a _ _, s => go a s
    | .set a _ v, s => go v (go a s)
    | .assertEq a b ret, s => go ret (go b (go a s))
    | .ioGetInfo key, s => go key s
    | .ioSetInfo key idx len ret, s => go ret (go len (go idx (go key s)))
    | .ioRead idx _, s => go idx s
    | .ioWrite data ret, s => go ret (go data s)
    | .debug _ (some t) ret, s => go ret (go t s)
    | .debug _ none ret, s => go ret s
    | .ann _ term, s => go term s
    | .data (.tuple ts), s => ts.foldl (fun s t => go t s) s
    | .data (.array ts), s => ts.foldl (fun s t => go t s) s
    | _, s => s

/-- Rewrite a Typ, resolving any typeRef whose name matches a template. -/
partial def rewriteImplicitTyp (resolveApp : Global → Global) : Typ → Typ
  | .typeRef g => .typeRef (resolveApp g)
  | .tuple ts => .tuple (ts.map (rewriteImplicitTyp resolveApp))
  | .array t n => .array (rewriteImplicitTyp resolveApp t) n
  | .pointer t => .pointer (rewriteImplicitTyp resolveApp t)
  | .function ins out =>
    .function (ins.map (rewriteImplicitTyp resolveApp)) (rewriteImplicitTyp resolveApp out)
  | t => t

mutual
/-- Rewrite Term.app and Pattern.ref names that match templates. -/
partial def rewriteImplicitTerm (resolveApp : Global → Global) : Term → Term
  | .app g args uc => .app (resolveApp g) (args.map (rewriteImplicitTerm resolveApp)) uc
  | .ann t term =>
    .ann (rewriteImplicitTyp resolveApp t) (rewriteImplicitTerm resolveApp term)
  | .let pat val body =>
    .let (rewriteImplicitPat resolveApp pat) (rewriteImplicitTerm resolveApp val)
      (rewriteImplicitTerm resolveApp body)
  | .match term branches =>
    .match (rewriteImplicitTerm resolveApp term)
      (branches.map fun (pat, t) =>
        (rewriteImplicitPat resolveApp pat, rewriteImplicitTerm resolveApp t))
  | .ret t => .ret (rewriteImplicitTerm resolveApp t)
  | .add a b => .add (rewriteImplicitTerm resolveApp a) (rewriteImplicitTerm resolveApp b)
  | .sub a b => .sub (rewriteImplicitTerm resolveApp a) (rewriteImplicitTerm resolveApp b)
  | .mul a b => .mul (rewriteImplicitTerm resolveApp a) (rewriteImplicitTerm resolveApp b)
  | .eqZero a => .eqZero (rewriteImplicitTerm resolveApp a)
  | .proj a n => .proj (rewriteImplicitTerm resolveApp a) n
  | .get a n => .get (rewriteImplicitTerm resolveApp a) n
  | .slice a i j => .slice (rewriteImplicitTerm resolveApp a) i j
  | .set a i v =>
    .set (rewriteImplicitTerm resolveApp a) i (rewriteImplicitTerm resolveApp v)
  | .store a => .store (rewriteImplicitTerm resolveApp a)
  | .load a => .load (rewriteImplicitTerm resolveApp a)
  | .ptrVal a => .ptrVal (rewriteImplicitTerm resolveApp a)
  | .assertEq a b ret =>
    .assertEq (rewriteImplicitTerm resolveApp a) (rewriteImplicitTerm resolveApp b)
      (rewriteImplicitTerm resolveApp ret)
  | .ioGetInfo key => .ioGetInfo (rewriteImplicitTerm resolveApp key)
  | .ioSetInfo key idx len ret =>
    .ioSetInfo (rewriteImplicitTerm resolveApp key) (rewriteImplicitTerm resolveApp idx)
      (rewriteImplicitTerm resolveApp len) (rewriteImplicitTerm resolveApp ret)
  | .ioRead idx len => .ioRead (rewriteImplicitTerm resolveApp idx) len
  | .ioWrite data ret =>
    .ioWrite (rewriteImplicitTerm resolveApp data) (rewriteImplicitTerm resolveApp ret)
  | .debug label term ret =>
    .debug label (term.map (rewriteImplicitTerm resolveApp)) (rewriteImplicitTerm resolveApp ret)
  | .data (.tuple ts) => .data (.tuple (ts.map (rewriteImplicitTerm resolveApp)))
  | .data (.array ts) => .data (.array (ts.map (rewriteImplicitTerm resolveApp)))
  | t => t
partial def rewriteImplicitPat (resolveApp : Global → Global) : Pattern → Pattern
  | .ref g pats => .ref (resolveApp g) (pats.map (rewriteImplicitPat resolveApp))
  | .tuple pats => .tuple (pats.map (rewriteImplicitPat resolveApp))
  | .array pats => .array (pats.map (rewriteImplicitPat resolveApp))
  | .or a b => .or (rewriteImplicitPat resolveApp a) (rewriteImplicitPat resolveApp b)
  | .pointer p => .pointer (rewriteImplicitPat resolveApp p)
  | p => p
end

mutual
partial def expandAliasesInTerm (expand : Typ → Typ) : Term → Term
  | .ann t term => .ann (expand t) (expandAliasesInTerm expand term)
  | .templateApp name tyArgs ctorOpt args uc =>
    .templateApp name (tyArgs.map expand) ctorOpt
      (args.map (expandAliasesInTerm expand)) uc
  | .let pat val body =>
    .let (expandAliasesInPat expand pat)
      (expandAliasesInTerm expand val) (expandAliasesInTerm expand body)
  | .match term branches =>
    .match (expandAliasesInTerm expand term)
      (branches.map fun (p, t) =>
        (expandAliasesInPat expand p, expandAliasesInTerm expand t))
  | .app g args uc => .app g (args.map (expandAliasesInTerm expand)) uc
  | .ret t => .ret (expandAliasesInTerm expand t)
  | .add a b => .add (expandAliasesInTerm expand a) (expandAliasesInTerm expand b)
  | .sub a b => .sub (expandAliasesInTerm expand a) (expandAliasesInTerm expand b)
  | .mul a b => .mul (expandAliasesInTerm expand a) (expandAliasesInTerm expand b)
  | .eqZero a => .eqZero (expandAliasesInTerm expand a)
  | .proj a n => .proj (expandAliasesInTerm expand a) n
  | .get a n => .get (expandAliasesInTerm expand a) n
  | .slice a i j => .slice (expandAliasesInTerm expand a) i j
  | .set a i v => .set (expandAliasesInTerm expand a) i (expandAliasesInTerm expand v)
  | .store a => .store (expandAliasesInTerm expand a)
  | .load a => .load (expandAliasesInTerm expand a)
  | .ptrVal a => .ptrVal (expandAliasesInTerm expand a)
  | .assertEq a b ret =>
    .assertEq (expandAliasesInTerm expand a) (expandAliasesInTerm expand b)
      (expandAliasesInTerm expand ret)
  | .ioGetInfo key => .ioGetInfo (expandAliasesInTerm expand key)
  | .ioSetInfo key idx len ret =>
    .ioSetInfo (expandAliasesInTerm expand key) (expandAliasesInTerm expand idx)
      (expandAliasesInTerm expand len) (expandAliasesInTerm expand ret)
  | .ioRead idx len => .ioRead (expandAliasesInTerm expand idx) len
  | .ioWrite data ret =>
    .ioWrite (expandAliasesInTerm expand data) (expandAliasesInTerm expand ret)
  | .debug label term ret =>
    .debug label (term.map (expandAliasesInTerm expand)) (expandAliasesInTerm expand ret)
  | .data (.tuple ts) => .data (.tuple (ts.map (expandAliasesInTerm expand)))
  | .data (.array ts) => .data (.array (ts.map (expandAliasesInTerm expand)))
  | t => t
partial def expandAliasesInPat (expand : Typ → Typ) : Pattern → Pattern
  | .templateRef name tyArgs ctor pats =>
    .templateRef name (tyArgs.map expand) ctor (pats.map (expandAliasesInPat expand))
  | .ref g pats => .ref g (pats.map (expandAliasesInPat expand))
  | .tuple pats => .tuple (pats.map (expandAliasesInPat expand))
  | .array pats => .array (pats.map (expandAliasesInPat expand))
  | .or a b => .or (expandAliasesInPat expand a) (expandAliasesInPat expand b)
  | .pointer p => .pointer (expandAliasesInPat expand p)
  | p => p
end

/--
Concretize all templates in a `Toplevel`, producing a `Toplevel` with only
concrete definitions. Performs a fixpoint iteration to handle transitive
template dependencies.
-/
partial def expandAliases (aliases : Array TypeAlias) : Typ → Typ
  | .typeRef g =>
    match aliases.find? (·.name == g) with
    | some alias => expandAliases aliases alias.expansion
    | none => .typeRef g
  | .tuple ts => .tuple (ts.map (expandAliases aliases))
  | .array t n => .array (expandAliases aliases t) n
  | .pointer t => .pointer (expandAliases aliases t)
  | .function ins out =>
    .function (ins.map (expandAliases aliases)) (expandAliases aliases out)
  | .templateApp name args => .templateApp name (args.map (expandAliases aliases))
  | t => t

def Toplevel.expandAllAliases (toplevel : Toplevel) : Toplevel :=
  if toplevel.typeAliases.isEmpty then toplevel
  else
    let expand := expandAliases toplevel.typeAliases
    let expandCtors (cs : List Constructor) := cs.map fun c =>
      { c with argTypes := c.argTypes.map expand }
    let expandInputs (ins : List (Local × Typ)) := ins.map fun (l, t) => (l, expand t)
    let expandTerm := expandAliasesInTerm expand
    { dataTypes := toplevel.dataTypes.map fun dt =>
        { dt with constructors := expandCtors dt.constructors }
      typeAliases := #[]
      functions := toplevel.functions.map fun f =>
        { f with inputs := expandInputs f.inputs
                 output := expand f.output
                 body := expandTerm f.body }
      dataTypeTemplates := toplevel.dataTypeTemplates.map fun dt =>
        { dt with constructors := expandCtors dt.constructors }
      functionTemplates := toplevel.functionTemplates.map fun ft =>
        { ft with inputs := expandInputs ft.inputs
                  output := expand ft.output
                  body := expandTerm ft.body } }

partial def Toplevel.concretize (toplevel : Toplevel) : Except String Toplevel := do
  if toplevel.dataTypeTemplates.isEmpty && toplevel.functionTemplates.isEmpty then
    return toplevel

  -- Expand type aliases in all types before concretization, so that
  -- List‹U64› and List‹[G; 8]› produce the same concretized name.
  let expand := expandAliases toplevel.typeAliases
  let expandCtors (cs : List Constructor) := cs.map fun c =>
    Constructor.mk c.nameHead (c.argTypes.map expand)
  let expandInputs (ins : List (Local × Typ)) := ins.map fun (l, t) => (l, expand t)
  -- Expand aliases in Term trees (for templateApp type args and annotations)
  let expandTerm := expandAliasesInTerm expand
  let toplevel : Toplevel := ⟨
    toplevel.dataTypes.map fun dt => DataType.mk dt.name (expandCtors dt.constructors),
    toplevel.typeAliases,
    toplevel.functions.map fun f =>
      Function.mk f.name (expandInputs f.inputs) (expand f.output) (expandTerm f.body) f.entry,
    toplevel.dataTypeTemplates.map fun dt =>
      DataTypeTemplate.mk dt.name dt.typeParams (expandCtors dt.constructors),
    toplevel.functionTemplates.map fun ft =>
      FunctionTemplate.mk ft.name ft.typeParams (expandInputs ft.inputs) (expand ft.output)
        (expandTerm ft.body)
  ⟩

  let dtTemplates : Std.HashMap Global DataTypeTemplate :=
    toplevel.dataTypeTemplates.foldl (init := {}) fun acc dt => acc.insert dt.name dt
  let fnTemplates : Std.HashMap Global FunctionTemplate :=
    toplevel.functionTemplates.foldl (init := {}) fun acc (fn' : FunctionTemplate) =>
      acc.insert fn'.name fn'

  -- Phase 1: resolve all explicit template refs in existing concrete definitions.
  -- `resolveAll` runs a ConcM action for each element, collecting the transformed
  -- array and all pending instantiations discovered along the way.
  let resolveAll {α β : Type} (arr : Array α) (f : α → ConcM β) :
      Except String (Array β × Array (Global × Array Typ × Bool)) :=
    (arr.mapM f).run #[]

  let (dataTypes, p1) ← resolveAll toplevel.dataTypes fun dt => do
    let constructors ← dt.constructors.mapM fun (ctor : Constructor) => do
      let argTypes ← ctor.argTypes.mapM (Typ.resolve dtTemplates fnTemplates)
      pure (Constructor.mk ctor.nameHead argTypes)
    pure (DataType.mk dt.name constructors)
  let (functions, p2) ← resolveAll toplevel.functions fun f => do
    let inputs ← f.inputs.mapM fun ((loc, t) : Local × Typ) =>
      return (loc, ← Typ.resolve dtTemplates fnTemplates t)
    let output ← Typ.resolve dtTemplates fnTemplates f.output
    let body ← Term.resolve dtTemplates fnTemplates f.body
    pure (Function.mk f.name inputs output body f.entry)
  let (typeAliases, p3) ← resolveAll toplevel.typeAliases fun ta => do
    let expansion ← Typ.resolve dtTemplates fnTemplates ta.expansion
    pure (TypeAlias.mk ta.name expansion)
  let mut pending := p1 ++ p2 ++ p3
  let mut dataTypes := dataTypes
  let mut functions := functions

  -- Phase 2: fixpoint - generate concrete definitions from templates
  let mut seen : Std.HashSet (Global × Array Typ) := {}
  while !pending.isEmpty do
    let batch := pending.filter fun (name, args, _) => !seen.contains (name, args)
    pending := #[]
    if batch.isEmpty then break
    for (name, args, isDT) in batch do
      if seen.contains (name, args) then continue
      seen := seen.insert (name, args)
      if isDT then
        let some tmpl := dtTemplates[name]? | throw s!"Unknown datatype template `{name}`"
        if args.size != tmpl.typeParams.size then
          throw s!"Template `{tmpl.name}` expects {tmpl.typeParams.size} type args, got {args.size}"
        let subst : TypeSubst := tmpl.typeParams.zip args
        let concName := concretizeName tmpl.name args
        let (constructors, newPending) ← (tmpl.constructors.mapM fun (ctor : Constructor) => do
          let argTypes ← ctor.argTypes.mapM (resolveTyp dtTemplates fnTemplates subst)
          pure (Constructor.mk ctor.nameHead argTypes)
        ).run #[]
        dataTypes := dataTypes.push (DataType.mk concName constructors)
        pending := pending ++ newPending
      else
        let some tmpl := fnTemplates[name]? | throw s!"Unknown function template `{name}`"
        if args.size != tmpl.typeParams.size then
          throw s!"Template `{tmpl.name}` expects {tmpl.typeParams.size} type args, got {args.size}"
        let subst : TypeSubst := tmpl.typeParams.zip args
        let concName := concretizeName tmpl.name args
        let ((inputs, output, body), newPending) ← (do
          let inputs ← tmpl.inputs.mapM fun ((loc, t) : Local × Typ) => do
            pure (loc, ← resolveTyp dtTemplates fnTemplates subst t)
          let output ← resolveTyp dtTemplates fnTemplates subst tmpl.output
          let body ← resolveTerm dtTemplates fnTemplates subst tmpl.body
          pure (inputs, output, body)
        ).run #[]
        functions := functions.push (Function.mk concName inputs output body false)
        pending := pending ++ newPending

  -- Phase 3: resolve implicit template refs per-function.
  -- For each function, discover which DT template instantiations are reachable
  -- (from own types + callee signatures), then resolve unqualified constructor
  -- names like `Option.Some` → `Option.G.Some` when unambiguous.

  -- Reverse maps: concretized name → template name
  let concToDtTemplate : Std.HashMap Global Global :=
    seen.fold (init := {}) fun acc (name, args) =>
      if dtTemplates.contains name then acc.insert (concretizeName name args) name
      else acc
  -- All concrete names (to avoid rewriting already-resolved names)
  let mut concreteNames : Std.HashSet Global := {}
  for dt in dataTypes do
    concreteNames := concreteNames.insert dt.name
    for ctor in dt.constructors do
      concreteNames := concreteNames.insert (dt.name.pushNamespace ctor.nameHead)
  for f in functions do
    concreteNames := concreteNames.insert f.name
  -- Function lookup for callee signature inspection
  let funcMap : Std.HashMap Global Function :=
    functions.foldl (init := {}) fun acc f => acc.insert f.name f

  functions := functions.map fun f => Id.run do
    -- Collect type refs from own signature + callee signatures (one hop)
    let mut typeRefs : Std.HashSet Global := {}
    for (_, t) in f.inputs do typeRefs := collectTypRefs t typeRefs
    typeRefs := collectTypRefs f.output typeRefs
    typeRefs := (collectCallTargets f.body).fold (init := typeRefs) fun refs target =>
      match funcMap[target]? with
      | some callee =>
        let refs := callee.inputs.foldl (fun refs (_, t) => collectTypRefs t refs) refs
        collectTypRefs callee.output refs
      | none => refs
    -- Build per-function DT instantiation map: template name → concretized names in scope
    let localDtMap := typeRefs.fold (init := (∅ : Std.HashMap Global (Array Global))) fun acc ref =>
      match concToDtTemplate[ref]? with
      | some tmplName => acc.insert tmplName ((acc.getD tmplName #[]).push ref)
      | none => acc
    -- Rewrite implicit refs when template has exactly one in-scope instantiation
    let resolveApp (name : Global) : Global :=
      if concreteNames.contains name then name
      -- Check constructor (parent is DT template)
      else if let some (ctor, parent) := name.popNamespace then
        match localDtMap[parent]? with
        | some #[concName] => concName.pushNamespace ctor
        | _ => name
      else name
    Function.mk f.name f.inputs f.output (rewriteImplicitTerm resolveApp f.body) f.entry

  pure ⟨dataTypes, typeAliases, functions, #[], #[]⟩

end Aiur

end
