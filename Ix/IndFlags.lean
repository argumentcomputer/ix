/-
  Ix.IndFlags: Lean's block-wide inductive flags, recomputed.

  Lean stores three block-wide flags on every `InductiveVal` of a mutual
  group: `isRec`, `isReflexive` and `numNested`. Ixon does not store them, so
  the decompiler recomputes them to rebuild an `InductiveVal`, and the compile
  drivers refuse an input group whose stored flags differ from the recomputed
  ones before any block is compiled (Rust `validate_ind_groups`).

  `numNested` is the number of auxiliary members of Lean's nested expansion
  (`elim_nested_inductive_fn`, `src/kernel/inductive.cpp`): a FIFO queue of
  types, initially the group's members in their order; each constructor of the
  head of the queue has its parameters opened and is walked in pre-order, a
  node `I Ds is` being a nested occurrence when `I` is an inductive outside the
  queue with at least `numParams I` arguments, some parameter argument `D`
  mentions a name in the queue, and no `D` mentions a variable bound inside the
  constructor; a new occurrence appends one auxiliary per member of `I`'s
  mutual group, instantiated at the occurrence's levels and parameters, to the
  end of the queue, and an occurrence already seen (compared exactly) is
  replaced by its auxiliary. `isRec` holds when some constructor field of the
  expanded block mentions a member, `isReflexive` when such a field is itself a
  function type. Mirrors Rust `compute_lean_ind_flags`.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public section

namespace Ix.IndFlags

open Ix.CompileM (CompileM CompileError arrIdx decomposeApps)

/-! ## Expression helpers -/

/-- Memoization cache for expression rewriters, keyed on the exact expression
    (`Ix.Compile.ExactKey.ExprKey`). -/
abbrev ExprCache := Std.HashMap Ix.Compile.ExactKey.ExprKey Expr

/-- A local declaration opened from a binder: its fresh variable's name, the
    binder's name, its domain and its binder information. -/
structure LocalDecl where
  fvarName : Name
  binderName : Name
  domain : Expr
  info : Lean.BinderInfo
  deriving Repr, Nonempty, Inhabited

/-- A fresh free variable named `_{pfx}_{idx}` (a single string component on
    the anonymous name, as Rust's `fresh_fvar` spells it). -/
def freshFVar (pfx : String) (idx : Nat) : Name × Expr :=
  let name := Name.mkStr .mkAnon s!"_{pfx}_{idx}"
  (name, Expr.mkFVar name)

/-- Apply an expression to a sequence of arguments: `f a1 a2 ... an`. -/
def mkAppN (f : Expr) (args : Array Expr) : Expr :=
  args.foldl Expr.mkApp f

/-- Shift loose bound variables `≥ cutoff` up by `amount`. -/
def shiftVars (expr : Expr) (amount : Nat) (cutoff : Nat) : Expr :=
  if amount == 0 then expr
  else match expr with
  | .bvar i _ =>
    if i >= cutoff then Expr.mkBVar (i + amount) else expr
  | .app f a _ =>
    Expr.mkApp (shiftVars f amount cutoff) (shiftVars a amount cutoff)
  | .lam n t b bi _ =>
    Expr.mkLam n (shiftVars t amount cutoff) (shiftVars b amount (cutoff + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (shiftVars t amount cutoff) (shiftVars b amount (cutoff + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (shiftVars t amount cutoff) (shiftVars v amount cutoff)
      (shiftVars b amount (cutoff + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (shiftVars e amount cutoff)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (shiftVars e amount cutoff)
  | _ => expr
termination_by structural expr

/-- Replace bound variable `depth` with `replacement` (not shifted), lowering
    the loose bound variables above it. -/
def instantiate1At (body : Expr) (replacement : Expr) (depth : Nat) : Expr :=
  match body with
  | .bvar i _ =>
    if i == depth then replacement
    else if i > depth then Expr.mkBVar (i - 1)
    else body
  | .app f a _ =>
    Expr.mkApp (instantiate1At f replacement depth) (instantiate1At a replacement depth)
  | .lam n t b bi _ =>
    Expr.mkLam n (instantiate1At t replacement depth)
      (instantiate1At b replacement (depth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (instantiate1At t replacement depth)
      (instantiate1At b replacement (depth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (instantiate1At t replacement depth)
      (instantiate1At v replacement depth)
      (instantiate1At b replacement (depth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (instantiate1At e replacement depth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (instantiate1At e replacement depth)
  | _ => body

/-- Lean's `instantiate1`: replace `bvar 0` with `replacement`. -/
def instantiate1 (body : Expr) (replacement : Expr) : Expr :=
  instantiate1At body replacement 0

/-- Simultaneous reverse instantiation under `depth` binders: `bvar (depth + i)`
    becomes `args[i]`, lifted by `depth`. -/
def instantiateRevAt (body : Expr) (args : Array Expr) (depth : Nat) : Expr :=
  let n := args.size
  match body with
  | .bvar i _ =>
    if i >= depth then
      let ridx := i - depth
      if h : ridx < args.size then
        shiftVars args[ridx] depth 0
      else
        Expr.mkBVar (i - n)
    else
      body
  | .app f a _ =>
    Expr.mkApp (instantiateRevAt f args depth) (instantiateRevAt a args depth)
  | .lam name t b bi _ =>
    Expr.mkLam name (instantiateRevAt t args depth)
      (instantiateRevAt b args (depth + 1)) bi
  | .forallE name t b bi _ =>
    Expr.mkForallE name (instantiateRevAt t args depth)
      (instantiateRevAt b args (depth + 1)) bi
  | .letE name t v b nd _ =>
    Expr.mkLetE name (instantiateRevAt t args depth)
      (instantiateRevAt v args depth)
      (instantiateRevAt b args (depth + 1)) nd
  | .proj name i e _ =>
    Expr.mkProj name i (instantiateRevAt e args depth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (instantiateRevAt e args depth)
  | _ => body
termination_by structural body

/-- Lean's `instantiate_rev`: `bvar i` becomes `args[i]` for `i < args.size`. -/
def instantiateRev (body : Expr) (args : Array Expr) : Expr :=
  if args.isEmpty then body
  else instantiateRevAt body args 0

/-- Peel `n` forall binders, substituting their variables with `args`
    (Lean's `instantiate_pi_params`). -/
def instantiatePiParams (typ : Expr) (n : Nat) (args : Array Expr) : Expr := Id.run do
  let mut cur := typ
  for arg in args.extract 0 n do
    match cur with
    | .forallE _ _ body _ _ =>
      cur := instantiateRev body #[arg]
    | _ => break
  return cur

/-- `(base, n)` with `level = succ^n base` and `base` not a successor. -/
def levelPeelSucc (l : Level) : Level × Nat := Id.run do
  let mut cur := l
  let mut n : Nat := 0
  repeat
    match cur with
    | .succ inner _ =>
      n := n + 1
      cur := inner
    | _ => break
  return (cur, n)

/-- `some (base, n)` iff the level is a numeral `succ^n zero`. -/
def levelExplicitOffset (l : Level) : Option (Level × Nat) :=
  let (base, n) := levelPeelSucc l
  match base with
  | .zero _ => some (base, n)
  | _ => none

/-- The digest-free key of a name: its components as a `Lean.Name`. -/
def nameKey : Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (nameKey p) s
  | .num p n _ => .num (nameKey p) n

/-- Level equality ignoring every stored digest. -/
def levelSameStructure : Level → Level → Bool
  | .zero _, .zero _ => true
  | .succ a _, .succ b _ => levelSameStructure a b
  | .max a b _, .max c d _ => levelSameStructure a c && levelSameStructure b d
  | .imax a b _, .imax c d _ => levelSameStructure a c && levelSameStructure b d
  | .param a _, .param b _ => nameKey a == nameKey b
  | .mvar a _, .mvar b _ => nameKey a == nameKey b
  | _, _ => false

/-- `max x y` with the kernel's simplifications: equal arguments, zero,
    numerals, the same base at different offsets, and absorption. -/
def levelMaxSmart (x y : Level) : Level := Id.run do
  if let (some (_, ox), some (_, oy)) := (levelExplicitOffset x, levelExplicitOffset y) then
    return if ox >= oy then x else y
  if levelSameStructure x y then
    return x
  if let .zero _ := x then
    return y
  if let .zero _ := y then
    return x
  if let .max bl br _ := y then
    if levelSameStructure bl x || levelSameStructure br x then
      return y
  if let .max al ar _ := x then
    if levelSameStructure al y || levelSameStructure ar y then
      return x
  let (baseX, offX) := levelPeelSucc x
  let (baseY, offY) := levelPeelSucc y
  if levelSameStructure baseX baseY then
    return if offX >= offY then x else y
  return Level.mkMax x y

/-- `imax x y` with the kernel's simplifications. -/
def levelImaxSmart (x y : Level) : Level := Id.run do
  if let .succ _ _ := y then
    return levelMaxSmart x y
  if let .zero _ := y then
    return y
  if let .zero _ := x then
    return y
  if let .succ inner _ := x then
    if let .zero _ := inner then
      return y
  if levelSameStructure x y then
    return x
  return Level.mkIMax x y

/-- Substitute universe parameters in a level, through the smart
    constructors. -/
partial def substLevel (lvl : Level) (params : Array Name) (univs : Array Level) : Level :=
  match lvl with
  | .zero _ | .mvar _ _ => lvl
  | .succ l _ => Level.mkSucc (substLevel l params univs)
  | .max a b _ =>
    levelMaxSmart (substLevel a params univs) (substLevel b params univs)
  | .imax a b _ =>
    levelImaxSmart (substLevel a params univs) (substLevel b params univs)
  | .param name _ => Id.run do
    for h : i in [0:params.size] do
      if hu : nameKey params[i] == nameKey name ∧ i < univs.size then
        return univs[i]'hu.2
    return lvl

/-- Substitute universe parameters in an expression. -/
def substLevels (expr : Expr) (params : Array Name) (univs : Array Level) : Expr :=
  if params.isEmpty || univs.isEmpty then expr
  else match expr with
  | .sort lvl _ => Expr.mkSort (substLevel lvl params univs)
  | .const name us _ =>
    Expr.mkConst name (us.map (substLevel · params univs))
  | .app f a _ =>
    Expr.mkApp (substLevels f params univs) (substLevels a params univs)
  | .lam n t b bi _ =>
    Expr.mkLam n (substLevels t params univs) (substLevels b params univs) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (substLevels t params univs) (substLevels b params univs) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (substLevels t params univs) (substLevels v params univs)
      (substLevels b params univs) nd
  | .proj n i e _ =>
    Expr.mkProj n i (substLevels e params univs)
  | .mdata md e _ =>
    Expr.mkMData md (substLevels e params univs)
  | _ => expr
termination_by structural expr

/-- Open up to `n` leading forall binders (through `mdata`) into fresh
    variables `_{pfx}_{startIdx + i}`: the variables, their declarations and
    the remaining body. -/
def forallTelescope (expr : Expr) (n : Nat) (pfx : String) (startIdx : Nat) :
    Array Expr × Array LocalDecl × Expr := Id.run do
  let mut fvars : Array Expr := #[]
  let mut decls : Array LocalDecl := #[]
  let mut cur := expr
  for i in [0:n] do
    repeat
      match cur with
      | .mdata _ inner _ => cur := inner
      | _ => break
    match cur with
    | .forallE name dom body bi _ =>
      let (fvName, fv) := freshFVar pfx (startIdx + i)
      decls := decls.push
        { fvarName := fvName, binderName := name, domain := dom, info := bi }
      fvars := fvars.push fv
      cur := instantiate1 body fv
    | _ => break
  return (fvars, decls, cur)

/-- Abstract the free variables at binder positions `lookup` gives (`0` the
    outermost) into bound variables, with `scopeDepth` of the binders in scope
    under `internalDepth` binders of the expression's own. -/
def batchAbstractWith (lookup : Name → Option Nat) (expr : Expr)
    (scopeDepth : Nat) (internalDepth : Nat) : Expr :=
  if scopeDepth == 0 then expr
  else match expr with
  | .fvar name _ =>
    match lookup name with
    | some pos =>
      if pos < scopeDepth then
        Expr.mkBVar ((scopeDepth - 1 - pos) + internalDepth)
      else
        expr
    | none => expr
  | .bvar i _ =>
    if i >= internalDepth then Expr.mkBVar (i + scopeDepth) else expr
  | .app f a _ =>
    Expr.mkApp (batchAbstractWith lookup f scopeDepth internalDepth)
      (batchAbstractWith lookup a scopeDepth internalDepth)
  | .lam n t b bi _ =>
    Expr.mkLam n (batchAbstractWith lookup t scopeDepth internalDepth)
      (batchAbstractWith lookup b scopeDepth (internalDepth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (batchAbstractWith lookup t scopeDepth internalDepth)
      (batchAbstractWith lookup b scopeDepth (internalDepth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (batchAbstractWith lookup t scopeDepth internalDepth)
      (batchAbstractWith lookup v scopeDepth internalDepth)
      (batchAbstractWith lookup b scopeDepth (internalDepth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (batchAbstractWith lookup e scopeDepth internalDepth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (batchAbstractWith lookup e scopeDepth internalDepth)
  | _ => expr

/-- Close `body` over `binders` (outermost first) as a forall chain. -/
def mkForall (body : Expr) (binders : Array LocalDecl) : Expr := Id.run do
  let k := binders.size
  if k == 0 then
    return body
  let mut fvarMap : Std.HashMap Lean.Name Nat := {}
  for (b, i) in binders.zipIdx do
    fvarMap := fvarMap.insert (nameKey b.fvarName) i
  let lookup := fun (n : Name) => fvarMap.get? (nameKey n)
  let mut result := batchAbstractWith lookup body k 0
  for (decl, j) in binders.zipIdx.reverse do
    let domain := batchAbstractWith lookup decl.domain j 0
    result := Expr.mkForallE decl.binderName domain result decl.info
  return result

/-- Whether any `const` or `proj` name in `expr` is in `names`. -/
def exprMentionsAnyName (expr : Expr) (names : Std.HashSet Ix.Compile.ExactKey.ExactName) : Bool := Id.run do
  if names.isEmpty then
    return false
  let mut stack : Array Expr := #[expr]
  repeat
    if let some e := stack.back? then
      stack := stack.pop
      match e with
      | .const n _ _ =>
        if names.contains n then
          return true
      | .app f a _ =>
        stack := stack.push f
        stack := stack.push a
      | .lam _ t b _ _ | .forallE _ t b _ _ =>
        stack := stack.push t
        stack := stack.push b
      | .letE _ t v b _ _ =>
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
      | .proj typeName _ val _ =>
        if names.contains typeName then
          return true
        stack := stack.push val
      | .mdata _ inner _ =>
        stack := stack.push inner
      | _ => pure ()
    else
      break
  return false

/-- Substitute free variables by name. -/
partial def replaceFVarsMap (e : Expr) (fvarMap : Std.HashMap Ix.Compile.ExactKey.ExactName Expr) : Expr :=
  match e with
  | .fvar n _ => (fvarMap.get? n).getD e
  | .app f a _ =>
    Expr.mkApp (replaceFVarsMap f fvarMap) (replaceFVarsMap a fvarMap)
  | .lam n t b bi _ =>
    Expr.mkLam n (replaceFVarsMap t fvarMap) (replaceFVarsMap b fvarMap) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (replaceFVarsMap t fvarMap) (replaceFVarsMap b fvarMap) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (replaceFVarsMap t fvarMap) (replaceFVarsMap v fvarMap)
      (replaceFVarsMap b fvarMap) nd
  | .proj n i s _ => Expr.mkProj n i (replaceFVarsMap s fvarMap)
  | .mdata md inner _ => Expr.mkMData md (replaceFVarsMap inner fvarMap)
  | _ => e

/-- Move an expression from a constructor's own parameter variables
    (`asFvars`) to the block's (`blockParamFvars`). -/
def replaceParamsExpr (e : Expr) (asFvars blockParamFvars : Array Expr) : Expr :=
  if asFvars.isEmpty then e
  else Id.run do
    let mut fvarMap : Std.HashMap Ix.Compile.ExactKey.ExactName Expr := {}
    for (localFv, blockFv) in asFvars.zip blockParamFvars do
      if let .fvar n _ := localFv then
        fvarMap := fvarMap.insert n blockFv
    return replaceFVarsMap e fvarMap

/-- Rewrite the result of an auxiliary constructor from
    `J spec_params indices` to `aux block_params indices`. -/
partial def replaceCtorResultHeadWithAux (e : Expr) (originalInd auxName : Name)
    (originalNParams : Nat) (blockLevels : Array Level)
    (blockParamFvars : Array Expr) : Expr :=
  match e with
  | .forallE n t b bi _ =>
    Expr.mkForallE n t
      (replaceCtorResultHeadWithAux b originalInd auxName originalNParams
        blockLevels blockParamFvars) bi
  | .mdata md inner _ =>
    Expr.mkMData md
      (replaceCtorResultHeadWithAux inner originalInd auxName originalNParams
        blockLevels blockParamFvars)
  | _ => Id.run do
    let (head, args) := decomposeApps e
    let .const headName _ _ := head | return e
    if headName != originalInd || args.size < originalNParams then
      return e
    let mut result := Expr.mkConst auxName blockLevels
    for param in blockParamFvars do
      result := Expr.mkApp result param
    for idxArg in args.toList.drop originalNParams do
      result := Expr.mkApp result idxArg
    return result

/-- Whether a parameter argument mentions a variable bound inside the
    constructor: a loose bound variable, or a free variable other than a block
    parameter. -/
def hasInvalidSpecRef (expr : Expr) (paramFvarNames : Array Name) : Bool := Id.run do
  let mut stack : Array (Expr × Nat) := #[(expr, 0)]
  while !stack.isEmpty do
    let some (e, depth) := stack.back? | break
    stack := stack.pop
    match e with
    | .bvar idx _ =>
      if idx ≥ depth then return true
    | .fvar n _ =>
      if !paramFvarNames.any (Ix.Compile.ExactKey.nameEq · n) then return true
    | .app f a _ =>
      stack := stack.push (f, depth) |>.push (a, depth)
    | .lam _ t b _ _ | .forallE _ t b _ _ =>
      stack := stack.push (t, depth) |>.push (b, depth + 1)
    | .letE _ t v b _ _ =>
      stack := stack.push (t, depth) |>.push (v, depth) |>.push (b, depth + 1)
    | .proj _ _ s _ => stack := stack.push (s, depth)
    | .mdata _ inner _ => stack := stack.push (inner, depth)
    | _ => pure ()
  return false

/-- Memoized "mentions any of these names" check. Unlike
    `exprMentionsAnyName`, a projection's type name is not consulted, only the
    projected value. -/
partial def hasIndOcc (e : Expr) (names : Std.HashSet Ix.Compile.ExactKey.ExactName)
    : StateM (Std.HashMap Ix.Compile.ExactKey.ExprKey Bool) Bool := do
  if let some cached := (← get).get? ⟨e⟩ then
    return cached
  let result ← match e with
    | .const name _ _ => pure (names.contains name)
    | .app f a _ => do
      if (← hasIndOcc f names) then pure true else hasIndOcc a names
    | .lam _ t b _ _ | .forallE _ t b _ _ => do
      if (← hasIndOcc t names) then pure true else hasIndOcc b names
    | .letE _ t v b _ _ => do
      if (← hasIndOcc t names) then pure true
      else if (← hasIndOcc v names) then pure true
      else hasIndOcc b names
    | .proj _ _ s _ => hasIndOcc s names
    | .mdata _ inner _ => hasIndOcc inner names
    | _ => pure false
  modify (·.insert ⟨e⟩ result)
  return result

/-! ## Lean's nested expansion -/

/-- A member of the expanded block (an original or an auxiliary) with its
    constructor types, nested occurrences replaced by auxiliaries. -/
structure Member where
  name : Name
  ctors : Array Expr
  deriving Inhabited

/-- The state of the expansion walk. `walkCache` memoizes one constructor's
    walk (its rewrites depend on the constructor's parameter variables). -/
structure ExpandSt where
  types : Array Member := #[]
  /-- The names of `types`, for membership. -/
  typeNameSet : Std.HashSet Ix.Compile.ExactKey.ExactName := {}
  /-- Each occurrence seen, compared exactly, with its auxiliary. -/
  seen : Std.HashMap Ix.Compile.ExactKey.ExprKey Name := {}
  nextAuxIdx : Nat := 1
  all0 : Name := default
  blockLevels : Array Level := #[]
  blockParamFvars : Array Expr := #[]
  blockParamDecls : Array LocalDecl := #[]
  blockParamFvarNames : Array Name := #[]
  walkCache : ExprCache := {}
  deriving Inhabited

abbrev ExpandM := StateT ExpandSt CompileM

/-- Append a member to the queue, keeping `typeNameSet` in sync. -/
def pushType (member : Member) : ExpandM Unit :=
  modify fun st => { st with
    typeNameSet := st.typeNameSet.insert member.name
    types := st.types.push member }

/-- A constant of the input, if any. -/
def lookupConst? (name : Name) : CompileM (Option ConstantInfo) := do
  pure ((← Ix.CompileM.getCompileEnv).env.get? name)

/-- If `e` is a nested occurrence, the expression that replaces it (opening
    auxiliaries for the external inductive's whole mutual group when the
    occurrence is new); `none` otherwise. Lean's `replace_if_nested`. -/
def replaceIfNested (e : Expr) (asFvars : Array Expr) : ExpandM (Option Expr) := do
  let (head, args) := decomposeApps e
  let .const headName headLevels _ := head | return none
  -- A member of the queue: direct recursion, not nesting.
  if (← get).typeNameSet.contains headName then
    return none
  let some (.inductInfo extInd) ← lookupConst? headName | return none
  let extNParams := extInd.numParams
  if args.size < extNParams then
    return none
  -- Some parameter argument must mention a member of the queue.
  let st ← get
  if !(args.toList.take extNParams).any
      (fun a => exprMentionsAnyName a st.typeNameSet) then
    return none
  let specParams : Array Expr :=
    (args.toList.take extNParams).toArray.map
      (fun sp => replaceParamsExpr sp asFvars st.blockParamFvars)
  for sp in specParams do
    if hasInvalidSpecRef sp st.blockParamFvarNames then
      return none
  let iAs := mkAppN (Expr.mkConst headName headLevels) specParams
  if let some auxName := st.seen.get? ⟨iAs⟩ then
    let mut result := Expr.mkConst auxName st.blockLevels
    for af in asFvars do
      result := Expr.mkApp result af
    for idxArg in args.toList.drop extNParams do
      result := Expr.mkApp result idxArg
    return some result
  -- A new occurrence: one auxiliary per member of the external group.
  let mut result : Option Expr := none
  for jName in extInd.all do
    let some (.inductInfo jInfo) ← lookupConst? jName | continue
    let auxIdx := (← get).nextAuxIdx
    let auxName := Name.mkStr (Name.mkStr (← get).all0 "_nested")
      s!"{jName.pretty.replace "." "_"}_{auxIdx}"
    modify fun s => { s with nextAuxIdx := s.nextAuxIdx + 1 }
    -- Every member `J As` of the group is seen under its own application, so
    -- a later occurrence of a sibling reuses its auxiliary.
    let jKey : Ix.Compile.ExactKey.ExprKey := ⟨mkAppN (Expr.mkConst jName headLevels) specParams⟩
    modify fun s =>
      if s.seen.contains jKey then s
      else { s with seen := s.seen.insert jKey auxName }
    let mut auxCtors : Array Expr := #[]
    for jCtorName in jInfo.ctors do
      let some (.ctorInfo jCtor) ← lookupConst? jCtorName | continue
      let ctorTypeInst :=
        substLevels jCtor.cnst.type jInfo.cnst.levelParams headLevels
      let ctorTypePeeled := instantiatePiParams ctorTypeInst extNParams specParams
      let ctorTypeBlock :=
        replaceParamsExpr ctorTypePeeled asFvars (← get).blockParamFvars
      let ctorTypeBlock := replaceCtorResultHeadWithAux ctorTypeBlock jName
        auxName extNParams (← get).blockLevels (← get).blockParamFvars
      auxCtors := auxCtors.push (mkForall ctorTypeBlock (← get).blockParamDecls)
    -- The head inductive's auxiliary replaces the occurrence.
    if headName == jName then
      let mut r := Expr.mkConst auxName (← get).blockLevels
      for af in asFvars do
        r := Expr.mkApp r af
      for idxArg in args.toList.drop extNParams do
        r := Expr.mkApp r idxArg
      result := some r
    pushType { name := auxName, ctors := auxCtors }
  return result

/-- Replace every nested occurrence, top-down, memoized per constructor.
    Lean's `replace_all_nested`. -/
partial def replaceAllNested (e : Expr) (asFvars : Array Expr) : ExpandM Expr := do
  if let some cached := (← get).walkCache.get? ⟨e⟩ then
    return cached
  if let some replaced ← replaceIfNested e asFvars then
    modify fun s => { s with walkCache := s.walkCache.insert ⟨e⟩ replaced }
    return replaced
  let result ← match e with
    | .app f a _ =>
      pure (Expr.mkApp (← replaceAllNested f asFvars) (← replaceAllNested a asFvars))
    | .lam n t b bi _ =>
      pure (Expr.mkLam n (← replaceAllNested t asFvars) (← replaceAllNested b asFvars) bi)
    | .forallE n t b bi _ =>
      pure (Expr.mkForallE n (← replaceAllNested t asFvars)
        (← replaceAllNested b asFvars) bi)
    | .letE n t v b nd _ =>
      pure (Expr.mkLetE n (← replaceAllNested t asFvars)
        (← replaceAllNested v asFvars) (← replaceAllNested b asFvars) nd)
    | .proj n i s _ =>
      pure (Expr.mkProj n i (← replaceAllNested s asFvars))
    | .mdata md inner _ =>
      pure (Expr.mkMData md (← replaceAllNested inner asFvars))
    | _ => pure e
  modify fun s => { s with walkCache := s.walkCache.insert ⟨e⟩ result }
  return result

/-- **Lean's nested expansion** of a group (`orderedOriginals`, the members
    in Lean's order): the members of the expanded block, originals first, then
    the auxiliaries in discovery order, and the number of originals. Lean's
    `elim_nested_inductive_fn`. -/
def expand (orderedOriginals : Array Name) : CompileM (Array Member × Nat) := do
  let some firstName := orderedOriginals[0]?
    | throw (.invalidMutualBlock "expand_nested_block: empty ordered_originals")
  let some (.inductInfo firstInd) ← lookupConst? firstName
    | throw (.missingConstant
        s!"{firstName} (expand_nested_block: first original not an inductive)")
  let nParams := firstInd.numParams
  let levelParams := firstInd.cnst.levelParams
  let blockLevels : Array Level := levelParams.map Level.mkParam
  let (blockParamFvars, blockParamDecls, _) :=
    forallTelescope firstInd.cnst.type nParams "bp" 0
  let blockParamFvarNames : Array Name := blockParamDecls.map (·.fvarName)
  let all0 := firstInd.all[0]?.getD firstName
  let init : ExpandSt := {
    all0, blockLevels, blockParamFvars, blockParamDecls, blockParamFvarNames }
  let build : ExpandM (Array Member × Nat) := do
    -- The queue starts with the originals.
    for name in orderedOriginals do
      let some (.inductInfo ind) ← lookupConst? name
        | throw (.missingConstant
            s!"{name} (expand_nested_block: original not an inductive)")
      let mut ctors : Array Expr := #[]
      for cn in ind.ctors do
        if let some (.ctorInfo c) ← lookupConst? cn then
          ctors := ctors.push c.cnst.type
      pushType { name, ctors }
    let nOriginals := (← get).types.size
    -- Each member's constructors, in queue order, with a fresh walk cache per
    -- constructor.
    let mut qi := 0
    while qi < (← get).types.size do
      let nCtors := (← arrIdx (← get).types qi "expandNestedBlock: queue member").ctors.size
      for ci in [0:nCtors] do
        let ctorType ← arrIdx (← arrIdx (← get).types qi "expandNestedBlock: queue member").ctors ci
          "expandNestedBlock: constructor"
        let (asFvars, asDecls, peeled) :=
          forallTelescope ctorType nParams "cp" (qi * 100 + ci)
        modify fun s => { s with walkCache := {} }
        let replaced ← replaceAllNested peeled asFvars
        let newCtorType := mkForall replaced asDecls
        modify fun s => { s with
          types := s.types.modify qi fun mem =>
            { mem with ctors := mem.ctors.modify ci fun _ => newCtorType } }
      qi := qi + 1
    return ((← get).types, nOriginals)
  Prod.fst <$> build.run init

/-! ## The flags -/

/-- A group's block-wide flags. Mirrors Rust `LeanIndFlags`. -/
structure LeanIndFlags where
  isRec : Bool
  isReflexive : Bool
  numNested : Nat
  deriving Repr, Inhabited

/-- **Lean's block-wide flags of a mutual group** (`all`, its members in
    Lean's order): `numNested` the expansion's auxiliaries, `isRec` whether a
    constructor field of the expanded block mentions a member, `isReflexive`
    whether such a field is a function type. Mirrors Rust
    `compute_lean_ind_flags`. -/
def computeLeanIndFlags (all : Array Name) : CompileM LeanIndFlags := do
  let (types, nOriginals) ← expand all
  let numNested := types.size - nOriginals
  let blockNames : Std.HashSet Ix.Compile.ExactKey.ExactName :=
    types.foldl (init := {}) fun s m => s.insert m.name
  let mut occCache : Std.HashMap Ix.Compile.ExactKey.ExprKey Bool := {}
  let mut isRec := false
  let mut isReflexive := false
  for member in types do
    for ctor in member.ctors do
      let mut ty := ctor
      let mut go := true
      while go do
        match ty with
        | .forallE _ dom body _ _ =>
          let (occ, cache') := (hasIndOcc dom blockNames).run occCache
          occCache := cache'
          if occ then
            isRec := true
            if let .forallE .. := dom then
              isReflexive := true
          ty := body
        | _ => go := false
  return { isRec, isReflexive, numNested }

/-- Refuse a group whose stored flags differ from Lean's (`computeLeanIndFlags`).
    A group with a member that is not an inductive, or a listed constructor
    that is not a constructor, is skipped (as Rust skips it). Mirrors Rust
    `validate_one_group`. -/
def validateIndGroup (all : Array Name) : CompileM Unit := do
  for member in all do
    match ← lookupConst? member with
    | some (.inductInfo v) =>
      for cn in v.ctors do
        match ← lookupConst? cn with
        | some (.ctorInfo _) => pure ()
        | _ => return
    | _ => return
  let flags ← computeLeanIndFlags all
  for member in all do
    let some (.inductInfo v) ← lookupConst? member | continue
    if v.isRec != flags.isRec || v.isReflexive != flags.isReflexive
        || v.numNested != flags.numNested then
      throw (.invalidMutualBlock
        s!"non-canonical inductive flags for '{member.pretty}': stored \
isRec={v.isRec} isReflexive={v.isReflexive} numNested={v.numNested}, \
computed isRec={flags.isRec} isReflexive={flags.isReflexive} \
numNested={flags.numNested}")

end Ix.IndFlags

end
