import Batteries.Data.RBMap
import Ix.TransportM
import Ix.Ixon.Metadata
import Ix.Ixon.Const
import Ix.Ixon.Serialize
import Ix.Common

open Batteries (RBMap)
open Batteries (RBSet)
open Ix.TransportM

namespace Ix.CanonM

inductive CanonMError
  | unknownConstant : Lean.Name → CanonMError
  | unfilledLevelMetavariable : Lean.Level → CanonMError
  | unfilledExprMetavariable : Lean.Expr → CanonMError
  | invalidBVarIndex : Nat → CanonMError
  | freeVariableExpr : Lean.Expr → CanonMError
  | metaVariableExpr : Lean.Expr → CanonMError
  | metaDataExpr : Lean.Expr → CanonMError
  | levelNotFound : Lean.Name → List Lean.Name → CanonMError
  | invalidConstantKind : Lean.Name → String → String → CanonMError
  | constantNotContentAddressed : Lean.Name → CanonMError
  | nonRecursorExtractedFromChildren : Lean.Name → CanonMError
  | cantFindMutDefIndex : Lean.Name → CanonMError
  | transportError : TransportError → CanonMError
  deriving Inhabited

instance : ToString CanonMError where toString
  | .unknownConstant n => s!"Unknown constant '{n}'"
  | .unfilledLevelMetavariable l => s!"Unfilled level metavariable on universe '{l}'"
  | .unfilledExprMetavariable e => s!"Unfilled level metavariable on expression '{e}'"
  | .invalidBVarIndex idx => s!"Invalid index {idx} for bound variable context"
  | .freeVariableExpr e => s!"Free variable in expression '{e}'"
  | .metaVariableExpr e => s!"Meta variable in expression '{e}'"
  | .metaDataExpr e => s!"Meta data in expression '{e}'"
  | .levelNotFound n ns => s!"'{n}' not found in '{ns}'"
  | .invalidConstantKind n ex gt =>
    s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
  | .constantNotContentAddressed n => s!"Constant '{n}' wasn't content-addressed"
  | .nonRecursorExtractedFromChildren n =>
    s!"Non-recursor '{n}' extracted from children"
  | .cantFindMutDefIndex n => s!"Can't find index for mutual definition '{n}'"
  | .transportError n => s!"Transport error '{repr n}'"

structure CanonMState where
  names  : RBMap Lean.Name (Address × Address) compare
  store  : RBMap Address Ixon.Const compare
  consts : RBMap Address (RBMap Address Ix.Const compare) compare
  commits: RBMap Ix.Const (Address × Address) compare
  blocks : RBSet (Address × Address) compare

structure CanonMCtx where
  constMap: Lean.ConstMap
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  recrCtx : RBMap Lean.Name Nat compare
  --quick : Bool
  --persist : Bool

abbrev CanonM := ReaderT CanonMCtx $ ExceptT CanonMError $ StateT CanonMState IO

def withBinder (name : Lean.Name) : CanonM α → CanonM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

def withLevelsAndReset (levels : List Lean.Name) : CanonM α → CanonM α :=
  withReader $ fun c =>
    { c with univCtx := levels, bindCtx := [], recrCtx := .empty }

def withRecrs (recrCtx : RBMap Lean.Name Nat compare) :
    CanonM α → CanonM α :=
  withReader $ fun c => { c with recrCtx := recrCtx }

def withLevels (lvls : List Lean.Name) : CanonM α → CanonM α :=
  withReader $ fun c => { c with univCtx := lvls }

def commit (const : Ix.Const) : CanonM (Address × Address) := do
  match (← get).commits.find? const with
  | some (contAddr, metaAddr) => pure (contAddr, metaAddr)
  | none => do
    let (ixon, meta) <- match constToIxon const with
      | .ok (i, m) => pure (i, m)
      | .error e => throw (.transportError e)
    let contAddr := Address.blake3 (Ixon.Serialize.put ixon)
    let metaAddr := Address.blake3 (Ixon.Serialize.put meta)
    modifyGet fun stt => ((contAddr, metaAddr), { stt with
      commits := stt.commits.insert const (contAddr, metaAddr)
      store := (stt.store.insert contAddr ixon).insert metaAddr meta
      consts := stt.consts.modify contAddr (fun m => m.insert metaAddr const)
    })

@[inline] def addConstToStt (name : Lean.Name) (constAddr metaAddr: Address) : CanonM Unit :=
  modify fun stt =>
    { stt with names := stt.names.insert name (constAddr, metaAddr) }

@[inline] def addBlockToStt (blockAddr blockMeta : Address) : CanonM Unit :=
  modify fun stt => { stt with blocks := stt.blocks.insert (blockAddr, blockMeta) }

scoped instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def concatOrds : List Ordering → Ordering :=
  List.foldl (· * ·) .eq

/-- Defines an ordering for Lean universes -/
def cmpLevel (x : Lean.Level) (y : Lean.Level) : CanonM Ordering :=
  match x, y with
  | .mvar .., _ => throw $ .unfilledLevelMetavariable x
  | _, .mvar .. => throw $ .unfilledLevelMetavariable y
  | .zero, .zero => return .eq
  | .zero, _ => return .lt
  | _, .zero => return .gt
  | .succ x, .succ y => cmpLevel x y
  | .succ .., _ => return .lt
  | _, .succ .. => return .gt
  | .max lx ly, .max rx ry => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .max .., _ => return .lt
  | _, .max .. => return .gt
  | .imax lx ly, .imax rx ry => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .imax .., _ => return .lt
  | _, .imax .. => return .gt
  | .param x, .param y => do
    let lvls := (← read).univCtx
    match (lvls.idxOf? x), (lvls.idxOf? y) with
    | some xi, some yi => return (compare xi yi)
    | none,    _       => throw $ .levelNotFound x lvls
    | _,       none    => throw $ .levelNotFound y lvls

/-- Canonicalizes a Lean universe level and adds it to the store -/
def canonUniv : Lean.Level → CanonM Ix.Univ
  | .zero => pure .zero
  | .succ u => return .succ (← canonUniv u)
  | .max a b  => return .max  (← canonUniv a) (← canonUniv b)
  | .imax a b => return .imax (← canonUniv a) (← canonUniv b)
  | .param name => do
    let lvls := (← read).univCtx
    match lvls.idxOf? name with
    | some n => pure $ .var name n
    | none   => throw $ .levelNotFound name lvls
  | l@(.mvar ..) => throw $ .unfilledLevelMetavariable l


/-- Retrieves a Lean constant from the environment by its name -/
def getLeanConstant (name : Lean.Name) : CanonM Lean.ConstantInfo := do
  match (← read).constMap.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : Bool :=
  match expr with
  | .forallE _ t e _  => match e with
    | .forallE ..  => isInternalRec e name
    | _ => isInternalRec t name -- t is the major premise
  | .app e .. => isInternalRec e name
  | .const n .. => n == name
  | _ => false

mutual

partial def canonConst (const : Lean.ConstantInfo) : CanonM (Address × Address) := do
  match (← get).names.find? const.name with
  | some (constAddr, metaAddr) => pure (constAddr, metaAddr)
  | none => match const with
    | .defnInfo val => withLevelsAndReset val.levelParams $ canonDefinition val
    | .inductInfo val => withLevelsAndReset val.levelParams $ canonInductive val
    | .ctorInfo val => do
      match ← getLeanConstant val.induct with
      | .inductInfo ind => discard $ canonConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
      canonConst const
    | .recInfo val => do
      match ← getLeanConstant val.getMajorInduct with
      | .inductInfo ind => discard $ canonConst (.inductInfo ind)
      | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
      canonConst const
    -- The rest adds the constants to the cache one by one
    | const => withLevelsAndReset const.levelParams do
      let obj ← match const with
        | .defnInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => unreachable!
        | .axiomInfo val =>
          pure $ .axiom ⟨val.levelParams.length, ← canonExpr val.type⟩
        | .thmInfo val =>
          -- Theorems are never truly recursive
          pure $ .theorem ⟨val.levelParams.length, ← canonExpr val.type,
            ← canonExpr val.value⟩
        | .opaqueInfo val =>
          let recrs := .single val.name 0
          pure $ .opaque ⟨val.levelParams.length, ← canonExpr val.type,
            ← withRecrs recrs $ canonExpr val.value⟩
        | .quotInfo val =>
          pure $ .quotient ⟨val.levelParams.length, ← canonExpr val.type, val.kind⟩
      let (constAddr, metaAddr) ← commit obj
      addConstToStt const.name constAddr metaAddr
      return (constAddr, metaAddr)

partial def canonDefinition (struct : Lean.DefinitionVal) : CanonM (Address × Address):= do
  -- If the mutual size is one, simply content address the single definition
  if struct.all matches [_] then
    let (constAddr, metaAddr) ← commit $ .definition
      (← withRecrs (.single struct.name 0) $ definitionToIR struct)
    addConstToStt struct.name constAddr metaAddr
    return (constAddr, metaAddr)

  -- Collecting and sorting all definitions in the mutual block
  let mutualDefs ← struct.all.mapM fun name => do
    match ← getLeanConstant name with
    | .defnInfo defn => pure defn
    | const => throw $ .invalidConstantKind const.name "definition" const.ctorName
  let mutualDefs ← sortDefs [mutualDefs]

  -- Building the `recrCtx`
  let mut recrCtx := default
  for (ds, i) in List.zipIdx mutualDefs do
    for d in ds do
      recrCtx := recrCtx.insert d.name i

  let definitions ← withRecrs recrCtx $ mutualDefs.mapM (·.mapM definitionToIR)

  -- Building and storing the block
  let definitionsIr := (definitions.map (match ·.head? with
    | some d => [d] | none => [])).flatten
  let (blockContAddr, blockMetaAddr) ← commit $ .mutDefBlock definitionsIr
  addBlockToStt blockContAddr blockMetaAddr

  -- While iterating on the definitions from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Address × Address) := none

  for name in struct.all do
    -- Storing and caching the definition projection
    -- Also adds the constant to the array of constants
    let some idx := recrCtx.find? name | throw $ .cantFindMutDefIndex name
    let (constAddr, metaAddr) ←
      commit $ .definitionProj ⟨blockContAddr, blockMetaAddr, idx⟩
    addConstToStt name constAddr metaAddr
    if struct.name == name then ret? := some (constAddr, metaAddr)

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed struct.name

partial def definitionToIR (defn : Lean.DefinitionVal) : CanonM Ix.Definition :=
  return ⟨defn.levelParams.length, ← canonExpr defn.type,
    ← canonExpr defn.value, defn.safety == .partial⟩

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the length of this function.
-/
partial def canonInductive (initInd : Lean.InductiveVal) : CanonM (Address × Address):= do
  -- `mutualConsts` is the list of the names of all constants associated with an inductive block
  -- it has the form: ind₁ ++ ctors₁ ++ recrs₁ ++ ... ++ indₙ ++ ctorsₙ ++ recrsₙ
  let mut inds := []
  let mut indCtors := []
  let mut indRecs := []
  let mut nameData : RBMap Lean.Name (List Lean.Name × List Lean.Name) compare
    := .empty
  for indName in initInd.all do
    match ← getLeanConstant indName with
    | .inductInfo ind =>
      let indRecrs := ((← read).constMap.childrenOfWith ind.name
        fun c => match c with | .recInfo _ => true | _ => false).map (·.name)
      inds := inds ++ [indName]
      indCtors := indCtors ++ ind.ctors
      indRecs := indRecs ++ indRecrs
      nameData := nameData.insert indName (ind.ctors, indRecrs)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName

  -- `mutualConsts` is the list of the names of all constants associated with an
  -- inductive block: the inductives themselves, the constructors and the recursors
  let mutualConsts := inds ++ indCtors ++ indRecs

  let recrCtx := mutualConsts.zipIdx.foldl (init := default)
    fun acc (n, i) => acc.insert n i

  -- This part will build the inductive block and add all inductives,
  -- constructors and recursors to `consts`
  let irInds ← initInd.all.mapM fun name => do match ← getLeanConstant name with
    | .inductInfo ind => withRecrs recrCtx do pure $ (← inductiveToIR ind)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
  let (blockContAddr, blockMetaAddr) ← commit $ .mutIndBlock irInds
  addBlockToStt blockContAddr blockMetaAddr

  -- While iterating on the inductives from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Address × Address) := none
  for (indName, indIdx) in initInd.all.zipIdx do
    -- Store and cache inductive projections
    let name := indName
    let (constAddr, metaAddr) ←
      commit $ .inductiveProj ⟨blockContAddr, blockMetaAddr, indIdx⟩
    addConstToStt name constAddr metaAddr
    if name == initInd.name then ret? := some (constAddr, metaAddr)

    let some (ctors, recrs) := nameData.find? indName
      | throw $ .cantFindMutDefIndex indName

    for (ctorName, ctorIdx) in ctors.zipIdx do
      -- Store and cache constructor projections
      let (constAddr, metaAddr) ←
        commit $ .constructorProj ⟨blockContAddr, blockMetaAddr, indIdx, ctorIdx⟩
      addConstToStt ctorName constAddr metaAddr

    for (recrName, recrIdx) in recrs.zipIdx do
      -- Store and cache recursor projections
      let (constAddr, metaAddr) ←
        commit $ .recursorProj ⟨blockContAddr, blockMetaAddr, indIdx, recrIdx⟩
      addConstToStt recrName constAddr metaAddr

  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed initInd.name

partial def inductiveToIR (ind : Lean.InductiveVal) : CanonM Ix.Inductive := do
  let leanRecs := (← read).constMap.childrenOfWith ind.name
    fun c => match c with | .recInfo _ => true | _ => false
  let (recs, ctors) ← leanRecs.foldrM (init := ([], []))
    fun r (recs, ctors) => match r with
      | .recInfo rv =>
        if isInternalRec rv.type ind.name then do
          let (thisRec, thisCtors) := ← internalRecToIR ind.ctors r
          pure (thisRec :: recs, thisCtors)
        else do
          let thisRec ← externalRecToIR r
          pure (thisRec :: recs, ctors)
      | _ => throw $ .nonRecursorExtractedFromChildren r.name
  let (struct, unit) ← if ind.isRec || ind.numIndices != 0 then pure (false, false) else
    match ctors with
    -- Structures can only have one constructor
    | [ctor] => pure (true, ctor.fields == 0)
    | _ => pure (false, false)
  return ⟨ind.levelParams.length, ← canonExpr ind.type, ind.numParams, ind.numIndices,
    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
    -- match the order used in `recrCtx`
    ctors, recs, ind.isRec, ind.isReflexive, struct, unit⟩

partial def internalRecToIR (ctors : List Lean.Name)
  : Lean.ConstantInfo → CanonM (Ix.Recursor × List Ix.Constructor)
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← canonExpr rec.type
    let (retCtors, retRules) ← rec.rules.foldrM (init := ([], []))
      fun r (retCtors, retRules) => do
        if ctors.contains r.ctor then
          let (ctor, rule) ← recRuleToIR r
          pure $ (ctor :: retCtors, rule :: retRules)
        else pure (retCtors, retRules) -- this is an external recursor rule
    let recr := ⟨rec.levelParams.length, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, retRules, rec.k, true⟩
    return (recr, retCtors)
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def recRuleToIR (rule : Lean.RecursorRule)
  : CanonM (Ix.Constructor × Ix.RecursorRule) := do
  let rhs ← canonExpr rule.rhs
  match ← getLeanConstant rule.ctor with
  | .ctorInfo ctor => withLevels ctor.levelParams do
    let typ ← canonExpr ctor.type
    let ctor := ⟨ctor.levelParams.length, typ, ctor.cidx, ctor.numParams, ctor.numFields⟩
    pure (ctor, ⟨rule.nfields, rhs⟩)
  | const => throw $ .invalidConstantKind const.name "constructor" const.ctorName

partial def externalRecToIR : Lean.ConstantInfo → CanonM Recursor
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← canonExpr rec.type
    let rules ← rec.rules.mapM externalRecRuleToIR
    return ⟨rec.levelParams.length, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, rules, rec.k, false⟩
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def externalRecRuleToIR (rule : Lean.RecursorRule) : CanonM RecursorRule :=
  return ⟨rule.nfields, ← canonExpr rule.rhs⟩

/--
Content-addresses a Lean expression and adds it to the store.

Constants are the tricky case, for which there are two possibilities:
* The constant belongs to `recrCtx`, representing a recursive call. Those are
encoded as variables with indexes that go beyond the bind indexes
* The constant doesn't belong to `recrCtx`, meaning that it's not a recursion
and thus we can canon the actual constant right away
-/
partial def canonExpr : Lean.Expr → CanonM Expr
  | .mdata _ e => canonExpr e
  | expr => match expr with
    | .bvar idx => do match (← read).bindCtx.get? idx with
      -- Bound variables must be in the bind context
      | some _ => return .var idx
      | none => throw $ .invalidBVarIndex idx
    | .sort lvl => return .sort $ ← canonUniv lvl
    | .const name lvls => do
      let univs ← lvls.mapM canonUniv
      match (← read).recrCtx.find? name with
      | some i => -- recursing!
        return .rec_ i univs
      | none => do
        let (contAddr, metaAddr) ← canonConst (← getLeanConstant name)
        return .const name contAddr metaAddr univs
    | .app fnc arg => return .app (← canonExpr fnc) (← canonExpr arg)
    | .lam name typ bod info =>
      return .lam name info (← canonExpr typ) (← withBinder name $ canonExpr bod)
    | .forallE name dom img info =>
      return .pi name info (← canonExpr dom) (← withBinder name $ canonExpr img)
    | .letE name typ exp bod nD =>
      return .letE name (← canonExpr typ) (← canonExpr exp)
        (← withBinder name $ canonExpr bod) nD
    | .lit lit => return .lit lit
    | .proj name idx exp => do
      let (contAddr, metaAddr) ← canonConst (← getLeanConstant name)
      return .proj name contAddr metaAddr idx (← canonExpr exp)
    | .fvar ..  => throw $ .freeVariableExpr expr
    | .mvar ..  => throw $ .metaVariableExpr expr
    | .mdata .. => throw $ .metaDataExpr expr

/--
A name-irrelevant ordering of Lean expressions.
`weakOrd` contains the best known current mutual ordering
-/
partial def cmpExpr (weakOrd : RBMap Lean.Name Nat compare) :
    Lean.Expr → Lean.Expr → CanonM Ordering
  | e@(.mvar ..), _ => throw $ .unfilledExprMetavariable e
  | _, e@(.mvar ..) => throw $ .unfilledExprMetavariable e
  | e@(.fvar ..), _ => throw $ .freeVariableExpr e
  | _, e@(.fvar ..) => throw $ .freeVariableExpr e
  | .mdata _ x, .mdata _ y  => cmpExpr weakOrd x y
  | .mdata _ x, y  => cmpExpr weakOrd x y
  | x, .mdata _ y  => cmpExpr weakOrd x y
  | .bvar x, .bvar y => return (compare x y)
  | .bvar .., _ => return .lt
  | _, .bvar .. => return .gt
  | .sort x, .sort y => cmpLevel x y
  | .sort .., _ => return .lt
  | _, .sort .. => return .gt
  | .const x xls, .const y yls => do
    let univs ← concatOrds <$> (xls.zip yls).mapM fun (x,y) => cmpLevel x y
    if univs != .eq then return univs
    match weakOrd.find? x, weakOrd.find? y with
    | some nx, some ny => return compare nx ny
    | none, some _ => return .gt
    | some _, none => return .lt
    | none, none =>
      return compare (← canonConst $ ← getLeanConstant x)
        (← canonConst $ ← getLeanConstant y)
  | .const .., _ => return .lt
  | _, .const .. => return .gt
  | .app xf xa, .app yf ya =>
    (· * ·) <$> cmpExpr weakOrd xf yf <*> cmpExpr weakOrd xa ya
  | .app .., _ => return .lt
  | _, .app .. => return .gt
  | .lam _ xt xb _, .lam _ yt yb _ =>
    (· * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xb yb
  | .lam .., _ => return .lt
  | _, .lam .. => return .gt
  | .forallE _ xt xb _, .forallE _ yt yb _ =>
    (· * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xb yb
  | .forallE .., _ => return .lt
  | _, .forallE .. => return .gt
  | .letE _ xt xv xb _, .letE _ yt yv yb _ =>
    (· * · * ·) <$> cmpExpr weakOrd xt yt <*> cmpExpr weakOrd xv yv <*> cmpExpr weakOrd xb yb
  | .letE .., _ => return .lt
  | _, .letE .. => return .gt
  | .lit x, .lit y =>
    return if x < y then .lt else if x == y then .eq else .gt
  | .lit .., _ => return .lt
  | _, .lit .. => return .gt
  | .proj _ nx tx, .proj _ ny ty => do
    let ts ← cmpExpr weakOrd tx ty
    return concatOrds [compare nx ny, ts]

/-- AST comparison of two Lean definitions.
  `weakOrd` contains the best known current mutual ordering -/
partial def cmpDef (weakOrd : RBMap Lean.Name Nat compare)
  (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
    CanonM Ordering := do
  let ls := compare x.levelParams.length y.levelParams.length
  let ts ← cmpExpr weakOrd x.type y.type
  let vs ← cmpExpr weakOrd x.value y.value
  return concatOrds [ls, ts, vs]

/-- AST equality between two Lean definitions.
  `weakOrd` contains the best known current mutual ordering -/
@[inline] partial def eqDef (weakOrd : RBMap Lean.Name Nat compare)
    (x y : Lean.DefinitionVal) : CanonM Bool :=
  return (← cmpDef weakOrd x y) == .eq

/--
`sortDefs` recursively sorts a list of mutual definitions into weakly equal blocks.
At each stage, we take as input the current best approximation of known weakly equal
blocks as a List of blocks, hence the `List (List DefinitionVal)` as the argument type.
We recursively take the input blocks and resort to improve the approximate known
weakly equal blocks, obtaining a sequence of list of blocks:
```
dss₀ := [startDefs]
dss₁ := sortDefs dss₀
dss₂ := sortDefs dss₁
dss₍ᵢ₊₁₎ := sortDefs dssᵢ ...
```
Initially, `startDefs` is simply the list of definitions we receive from `DefinitionVal.all`;
since there is no order yet, we treat it as one block all weakly equal. On the other hand,
at the end, there is some point where `dss₍ᵢ₊₁₎ := dssᵢ`, then we have hit a fixed point
and we may end the sorting process. (We claim that such a fixed point exists, although
technically we don't really have a proof.)

On each iteration, we hope to improve our knowledge of weakly equal blocks and use that
knowledge in the next iteration. e.g. We start with just one block with everything in it,
but the first sort may differentiate the one block into 3 blocks. Then in the second
iteration, we have more information than than first, since the relationship of the 3 blocks
gives us more information; this information may then be used to sort again, turning 3 blocks
into 4 blocks, and again 4 blocks into 6 blocks, etc, until we have hit a fixed point.
This step is done in the computation of `newDss` and then comparing it to the original `dss`.

Two optimizations:

1. `names := enum dss` records the ordering information in a map for faster access.
    Directly using `List.findIdx?` on dss is slow and introduces `Option` everywhere.
    `names` is used as a custom comparison in `ds.sortByM (cmpDef names)`.
2. `normDss/normNewDss`. We want to compare if two lists of blocks are equal.
    Technically blocks are sets and their order doesn't matter, but we have encoded
    them as lists. To fix this, we sort the list by name before comparing. Note we
    could maybe also use `List (RBTree ..)` everywhere, but it seemed like a hassle.
-/
partial def sortDefs (dss : List (List Lean.DefinitionVal)) :
    CanonM (List (List Lean.DefinitionVal)) := do
  let enum (ll : List (List Lean.DefinitionVal)) :=
    RBMap.ofList (ll.zipIdx.map fun (xs, n) => xs.map (·.name, n)).flatten
  let weakOrd := enum dss _
  let newDss ← (← dss.mapM fun ds =>
    match ds with
    | []  => unreachable!
    | [d] => pure [[d]]
    | ds  => do pure $ (← List.groupByM (eqDef weakOrd) $
      ← ds.sortByM (cmpDef weakOrd))).joinM

  -- must normalize, see comments
  let normDss    := dss.map    fun ds => ds.map (·.name) |>.sort
  let normNewDss := newDss.map fun ds => ds.map (·.name) |>.sort
  if normDss == normNewDss then return newDss
  else sortDefs newDss

end

end Ix.CanonM
