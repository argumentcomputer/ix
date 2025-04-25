import Batteries.Data.RBMap
import Ix.TransportM
import Ix.Ixon.Metadata
import Ix.Ixon.Const
import Ix.Ixon.Serialize
import Ix.Common
import Ix.Store

open Batteries (RBMap)
open Batteries (RBSet)
open Ix.TransportM

namespace Ix.Compile

inductive CompileError
| unknownConstant : Lean.Name → CompileError
| unfilledLevelMetavariable : Lean.Level → CompileError
| unfilledExprMetavariable : Lean.Expr → CompileError
| invalidBVarIndex : Nat → CompileError
| freeVariableExpr : Lean.Expr → CompileError
| metaVariableExpr : Lean.Expr → CompileError
| metaDataExpr : Lean.Expr → CompileError
| levelNotFound : Lean.Name → List Lean.Name → CompileError
| invalidConstantKind : Lean.Name → String → String → CompileError
| constantNotContentAddressed : Lean.Name → CompileError
| nonRecursorExtractedFromChildren : Lean.Name → CompileError
| cantFindMutDefIndex : Lean.Name → CompileError
| transportError : TransportError → CompileError
| kernelException : Lean.Kernel.Exception → CompileError
| cantPackLevel : Nat → CompileError

def CompileError.pretty : CompileError -> IO String
| .unknownConstant n => pure s!"Unknown constant '{n}'"
| .unfilledLevelMetavariable l => pure s!"Unfilled level metavariable on universe '{l}'"
| .unfilledExprMetavariable e => pure s!"Unfilled level metavariable on expression '{e}'"
| .invalidBVarIndex idx => pure s!"Invalid index {idx} for bound variable context"
| .freeVariableExpr e => pure s!"Free variable in expression '{e}'"
| .metaVariableExpr e => pure s!"Metavariable in expression '{e}'"
| .metaDataExpr e => pure s!"Meta data in expression '{e}'"
| .levelNotFound n ns => pure s!"'Level {n}' not found in '{ns}'"
| .invalidConstantKind n ex gt => pure s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
| .constantNotContentAddressed n => pure s!"Constant '{n}' wasn't content-addressed"
| .nonRecursorExtractedFromChildren n => pure
  s!"Non-recursor '{n}' extracted from children"
| .cantFindMutDefIndex n => pure s!"Can't find index for mutual definition '{n}'"
| .transportError n => pure s!"Transport error '{repr n}'"
| .kernelException e => (·.pretty 80) <$> (e.toMessageData .empty).format
| .cantPackLevel n => pure s!"Can't pack level {n} greater than 2^256'"

structure CompileEnv where
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  mutCtx  : RBMap Lean.Name Nat compare
  maxHeartBeats: USize

def CompileEnv.init (maxHeartBeats: USize): CompileEnv :=
  ⟨default, default, default, maxHeartBeats⟩

structure CompileState where
  env: Lean.Environment
  prng: StdGen
  names: RBMap Lean.Name (Address × Address) compare
  store: RBMap Address Ixon.Const compare
  cache: RBMap Ix.Const (Address × Address) compare
  comms: RBMap Lean.Name (Address × Address) compare
  axioms: RBMap Lean.Name (Address × Address) compare
  blocks: RBSet (Address × Address) compare

def CompileState.init (env: Lean.Environment) (seed: Nat): CompileState :=
  ⟨env, mkStdGen seed, default, default, default, default, default, default⟩

abbrev CompileM := ReaderT CompileEnv <| EStateM CompileError CompileState

def CompileM.run (env: CompileEnv) (stt: CompileState) (c : CompileM α)
  : EStateM.Result CompileError CompileState α
  := EStateM.run (ReaderT.run c env) stt

def storeConst (const: Ixon.Const): CompileM Address := do
  let addr := Address.blake3 (Ixon.Serialize.put const)
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr const
  })

def randByte (lo hi: Nat): CompileM Nat := do
  modifyGet fun s => 
  let (res, g') := randNat s.prng lo hi
  (res, {s with prng := g'})

def freshSecret : CompileM Address := do
  let mut secret: ByteArray := default
  for _ in [:32] do
    let rand <- randByte 0 255
    secret := secret.push rand.toUInt8
  return ⟨secret⟩

-- add binding name to local context
def withBinder
  {m : Type -> Type} {α : Type}
  [Monad m] [MonadWithReader CompileEnv m]
  (name: Lean.Name) 
  : m α -> m α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def withLevels
  {m : Type -> Type} {α : Type}
  [Monad m] [MonadWithReader CompileEnv m]
  (lvls : List Lean.Name) 
  : m α -> m α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def withMutCtx
  {m : Type -> Type} {α : Type}
  [Monad m] [MonadWithReader CompileEnv m]
  (mutCtx : RBMap Lean.Name Nat compare) 
  : m α -> m α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

-- reset local context
def resetCtx : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := [], bindCtx := [], mutCtx := .empty }

def resetCtxWithLevels (lvls: List Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := lvls, bindCtx := [], mutCtx := .empty }

-- lookup or compute the addresses of a constant
def hashConst (const: Ix.Const) : CompileM (Address × Address) := do
  match (<- get).cache.find? const with
  | some (anonAddr, metaAddr) => pure (anonAddr, metaAddr)
  | none => do
    let (anonIxon, metaIxon) <- match constToIxon const with
      | .ok (a, m) => pure (a, m)
      | .error e => throw (.transportError e)
    let anonAddr <- storeConst anonIxon
    let metaAddr <- storeConst metaIxon
    modifyGet fun stt => ((anonAddr, metaAddr), { stt with
      cache := stt.cache.insert const (anonAddr, metaAddr)
    })

scoped instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def concatOrds : List Ordering → Ordering :=
  List.foldl (· * ·) .eq

/-- Defines an ordering for Lean universes -/
def compareLevel (x : Lean.Level) (y : Lean.Level) : CompileM Ordering :=
  match x, y with
  | .mvar .., _ => throw $ .unfilledLevelMetavariable x
  | _, .mvar .. => throw $ .unfilledLevelMetavariable y
  | .zero, .zero => return .eq
  | .zero, _ => return .lt
  | _, .zero => return .gt
  | .succ x, .succ y => compareLevel x y
  | .succ .., _ => return .lt
  | _, .succ .. => return .gt
  | .max lx ly, .max rx ry => 
    (· * ·) <$> compareLevel lx rx <*> compareLevel ly ry
  | .max .., _ => return .lt
  | _, .max .. => return .gt
  | .imax lx ly, .imax rx ry => 
    (· * ·) <$> compareLevel lx rx <*> compareLevel ly ry
  | .imax .., _ => return .lt
  | _, .imax .. => return .gt
  | .param x, .param y => do
    let lvls := (← read).univCtx
    match (lvls.idxOf? x), (lvls.idxOf? y) with
    | some xi, some yi => return (compare xi yi)
    | none,    _       => throw $ .levelNotFound x lvls
    | _,       none    => throw $ .levelNotFound y lvls

/-- Canonicalizes a Lean universe level and adds it to the store -/
def compileLevel : Lean.Level → CompileM Ix.Univ
| .zero => pure .zero
| .succ u => return .succ (← compileLevel u)
| .max a b  => return .max (← compileLevel a) (← compileLevel b)
| .imax a b => return .imax (← compileLevel a) (← compileLevel b)
| .param name => do
  let lvls := (← read).univCtx
  match lvls.idxOf? name with
  | some n => pure $ .var name n
  | none   => throw $ .levelNotFound name lvls
| l@(.mvar ..) => throw $ .unfilledLevelMetavariable l

/-- Retrieves a Lean constant from the environment by its name -/
def findLeanConst (name : Lean.Name) : CompileM Lean.ConstantInfo := do
  match (← get).env.constants.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name

/-- Check if expression is an internal recursor --/
def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : Bool :=
  match expr with
  | .forallE _ t e _  => match e with
    | .forallE ..  => isInternalRec e name
    | _ => isInternalRec t name -- t is the major premise
  | .app e .. => isInternalRec e name
  | .const n .. => n == name
  | _ => false

mutual

/-- compile Lean Constant --/
partial def compileConst (const : Lean.ConstantInfo)
  : CompileM (Address × Address) := do
  match (← get).names.find? const.name with
  | some (anonAddr, metaAddr) => pure (anonAddr, metaAddr)
  | none => match const with
    | .defnInfo val =>
      resetCtxWithLevels val.levelParams $ compileDefinition val
    | .inductInfo val => 
      resetCtxWithLevels val.levelParams $ compileInductive val
    | .ctorInfo val => do
      match ← findLeanConst val.induct with
      | .inductInfo ind => discard $ compileConst (.inductInfo ind)
      | const =>
        throw $ .invalidConstantKind const.name "inductive" const.ctorName
      -- this should return by finding the ctor in names via the above some case
      compileConst const
    | .recInfo val => do
      match ← findLeanConst val.getMajorInduct with
      | .inductInfo ind => discard $ compileConst (.inductInfo ind)
      | const =>
        throw $ .invalidConstantKind const.name "inductive" const.ctorName
      -- this should return by finding the recr in names via the above some case
      compileConst const
    -- The rest adds the constants to the cache one by one
    | .axiomInfo val => resetCtxWithLevels const.levelParams do
      let c := .axiom ⟨val.levelParams, ← compileExpr val.type⟩
      let (anonAddr, metaAddr) ← hashConst c
      modify fun stt => { stt with
        axioms := stt.axioms.insert const.name (anonAddr, metaAddr)
        names := stt.names.insert const.name (anonAddr, metaAddr)
      }
      return (anonAddr, metaAddr)
    | .thmInfo val => resetCtxWithLevels const.levelParams do
      let type <- compileExpr val.type
      let value <- compileExpr val.value
      let c := .theorem ⟨val.levelParams, type, value⟩
      let (anonAddr, metaAddr) ← hashConst c
      modify fun stt => { stt with
        names := stt.names.insert const.name (anonAddr, metaAddr)
      }
      return (anonAddr, metaAddr)
    | .opaqueInfo val => resetCtxWithLevels const.levelParams do
      let mutCtx := .single val.name 0
      let type <- compileExpr val.type
      let value <- withMutCtx mutCtx $ compileExpr val.value
      let c := .opaque ⟨val.levelParams, type, value⟩
      let (anonAddr, metaAddr) ← hashConst c
      modify fun stt => { stt with
        names := stt.names.insert const.name (anonAddr, metaAddr)
      }
      return (anonAddr, metaAddr)
    | .quotInfo val => resetCtxWithLevels const.levelParams do
      let type <- compileExpr val.type
      let c := .quotient ⟨val.levelParams, type, val.kind⟩
      let (anonAddr, metaAddr) ← hashConst c
      modify fun stt => { stt with
        axioms := (stt.axioms.insert const.name (anonAddr, metaAddr))
        names := stt.names.insert const.name (anonAddr, metaAddr)
      }
      return (anonAddr, metaAddr)

/-- compile possibly mutual Lean definition --/
partial def compileDefinition (struct: Lean.DefinitionVal)
  : CompileM (Address × Address) := do
  -- If the mutual size is one, simply content address the single definition
  if struct.all matches [_] then
    let defn <- withMutCtx (.single struct.name 0) $ definitionToIR struct
    let (anonAddr, metaAddr) <- hashConst $ .definition defn
    modify fun stt => { stt with
      names := stt.names.insert struct.name (anonAddr, metaAddr)
    }
    return (anonAddr, metaAddr)
  -- Collecting and sorting all definitions in the mutual block
  let mutualDefs <- struct.all.mapM fun name => do
    match <- findLeanConst name with
      | .defnInfo defn => pure defn
      | const => 
        throw $ .invalidConstantKind const.name "definition" const.ctorName
  let mutualDefs <- sortDefs [mutualDefs]
  -- Building the `mutCtx`
  let mut mutCtx := default
  for (ds, i) in List.zipIdx mutualDefs do
    for d in ds do
      mutCtx := mutCtx.insert d.name i
  let definitions ← withMutCtx mutCtx $ mutualDefs.mapM (·.mapM definitionToIR)
  -- Building and storing the block
  -- TODO: check if this flatten call actually makes sense
  let definitionsIR := (definitions.map (match ·.head? with
    | some d => [d] | none => [])).flatten
  let (blockAnonAddr, blockMetaAddr) ← hashConst $ .mutDefBlock definitionsIR
  modify fun stt =>
    { stt with blocks := stt.blocks.insert (blockAnonAddr, blockMetaAddr) }
  -- While iterating on the definitions from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Address × Address) := none
  for name in struct.all do
    -- Storing and caching the definition projection
    -- Also adds the constant to the array of constants
    let some idx := mutCtx.find? name | throw $ .cantFindMutDefIndex name
    let (anonAddr, metaAddr) ←
      hashConst $ .definitionProj ⟨blockAnonAddr, blockMetaAddr, idx⟩
    modify fun stt => { stt with
      names := stt.names.insert name (anonAddr, metaAddr)
    }
    if struct.name == name then ret? := some (anonAddr, metaAddr)
  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed struct.name


partial def definitionToIR (defn: Lean.DefinitionVal)
  : CompileM Ix.Definition := do
  let type <- compileExpr defn.type
  let value <- compileExpr defn.value
  return ⟨defn.levelParams, type, value, defn.safety == .partial⟩

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the complexity of this function.
-/
partial def compileInductive (initInd: Lean.InductiveVal) 
  : CompileM (Address × Address) := do
  let mut inds := []
  let mut indCtors := []
  let mut indRecs := []
  let mut nameData : RBMap Lean.Name (List Lean.Name × List Lean.Name) compare
    := .empty
  for indName in initInd.all do
    match ← findLeanConst indName with
    | .inductInfo ind =>
      let indRecrs := ((← get).env.constants.childrenOfWith ind.name
        fun c => match c with | .recInfo _ => true | _ => false).map (·.name)
      inds := inds ++ [indName]
      indCtors := indCtors ++ ind.ctors
      indRecs := indRecs ++ indRecrs
      nameData := nameData.insert indName (ind.ctors, indRecrs)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
  -- `mutualConsts` is the list of the names of all constants associated with an
  -- inductive block: the inductives themselves, the constructors and the recursors
  let mutualConsts := inds ++ indCtors ++ indRecs
  let mutCtx := mutualConsts.zipIdx.foldl (init := default)
    fun acc (n, i) => acc.insert n i
  -- This part builds the inductive block
  -- and adds all inductives, constructors and recursors to `consts`
  let irInds ← initInd.all.mapM fun name => do match ← findLeanConst name with
    | .inductInfo ind => withMutCtx mutCtx do pure $ (← inductiveToIR ind)
    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
  let (blockAnonAddr, blockMetaAddr) ← hashConst $ .mutIndBlock irInds
  modify fun stt =>
    { stt with blocks := stt.blocks.insert (blockAnonAddr, blockMetaAddr) }
  -- While iterating on the inductives from the mutual block, we need to track
  -- the correct objects to return
  let mut ret? : Option (Address × Address) := none
  for (indName, indIdx) in initInd.all.zipIdx do
    -- Store and cache inductive projections
    let name := indName
    let (anonAddr, metaAddr) ←
      hashConst $ .inductiveProj ⟨blockAnonAddr, blockMetaAddr, indIdx⟩
    modify fun stt => { stt with
      names := stt.names.insert name (anonAddr, metaAddr)
    }
    if name == initInd.name then ret? := some (anonAddr, metaAddr)
    let some (ctors, recrs) := nameData.find? indName
      | throw $ .cantFindMutDefIndex indName
    for (ctorName, ctorIdx) in ctors.zipIdx do
      -- Store and cache constructor projections
      let (anonAddr, metaAddr) ←
        hashConst $ .constructorProj
          ⟨blockAnonAddr, blockMetaAddr, indIdx, ctorIdx⟩
      modify fun stt => { stt with
        names := stt.names.insert ctorName (anonAddr, metaAddr)
      }
    for (recrName, recrIdx) in recrs.zipIdx do
      -- Store and cache recursor projections
      let (anonAddr, metaAddr) ←
        hashConst $ .recursorProj
          ⟨blockAnonAddr, blockMetaAddr, indIdx, recrIdx⟩
      modify fun stt => { stt with
        names := stt.names.insert recrName (anonAddr, metaAddr)
      }
  match ret? with
  | some ret => return ret
  | none => throw $ .constantNotContentAddressed initInd.name

partial def inductiveToIR (ind : Lean.InductiveVal) : CompileM Ix.Inductive := do
  let leanRecs := (← get).env.constants.childrenOfWith ind.name
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
  let (struct, unit) ← if ind.isRec || ind.numIndices != 0 
  then pure (false, false)
  else
    match ctors with
    -- Structures can only have one constructor
    | [ctor] => pure (true, ctor.fields == 0)
    | _ => pure (false, false)
  return ⟨ind.levelParams, ← compileExpr ind.type, ind.numParams, ind.numIndices,
    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
    -- match the order used in `recrCtx`
    ctors, recs, ind.isRec, ind.isReflexive, struct, unit⟩

partial def internalRecToIR (ctors : List Lean.Name)
  : Lean.ConstantInfo → CompileM (Ix.Recursor × List Ix.Constructor)
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← compileExpr rec.type
    let (retCtors, retRules) ← rec.rules.foldrM (init := ([], []))
      fun r (retCtors, retRules) => do
        if ctors.contains r.ctor then
          let (ctor, rule) ← recRuleToIR r
          pure $ (ctor :: retCtors, rule :: retRules)
        else pure (retCtors, retRules) -- this is an external recursor rule
    let recr := ⟨rec.levelParams, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, retRules, rec.k, true⟩
    return (recr, retCtors)
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def recRuleToIR (rule : Lean.RecursorRule)
  : CompileM (Ix.Constructor × Ix.RecursorRule) := do
  let rhs ← compileExpr rule.rhs
  match ← findLeanConst rule.ctor with
  | .ctorInfo ctor => withLevels ctor.levelParams do
    let typ ← compileExpr ctor.type
    let ctor :=
      ⟨ctor.levelParams, typ, ctor.cidx, ctor.numParams, ctor.numFields⟩
    pure (ctor, ⟨rule.nfields, rhs⟩)
  | const =>
    throw $ .invalidConstantKind const.name "constructor" const.ctorName

partial def externalRecToIR : Lean.ConstantInfo → CompileM Recursor
  | .recInfo rec => withLevels rec.levelParams do
    let typ ← compileExpr rec.type
    let rules ← rec.rules.mapM externalRecRuleToIR
    return ⟨rec.levelParams, typ, rec.numParams, rec.numIndices,
      rec.numMotives, rec.numMinors, rules, rec.k, false⟩
  | const => throw $ .invalidConstantKind const.name "recursor" const.ctorName

partial def externalRecRuleToIR (rule : Lean.RecursorRule) 
  : CompileM RecursorRule :=
  return ⟨rule.nfields, ← compileExpr rule.rhs⟩

/--
Content-addresses a Lean expression and adds it to the store.

Constants are the tricky case, for which there are two possibilities:
* The constant belongs to `mutCtx`, representing a recursive call. Those are
encoded as `.rec_` with indexes based on order in the mutual definition
* The constant doesn't belong to `mutCtx`, meaning that it's not a recursion
and thus we can canon the actual constant right away
-/
partial def compileExpr : Lean.Expr → CompileM Expr
| .mdata _ e => compileExpr e
| expr => match expr with
  | .bvar idx => do match (← read).bindCtx[idx]? with
    -- Bound variables must be in the bind context
    | some _ => return .var idx
    | none => throw $ .invalidBVarIndex idx
  | .sort lvl => return .sort $ ← compileLevel lvl
  | .const name lvls => do
    let univs ← lvls.mapM compileLevel
    match (← read).mutCtx.find? name with
    -- recursing!
    | some i => return .rec_ name i univs
    | none => match (<- get).comms.find? name with
      | some (commAddr, metaAddr) => do
        return .const name commAddr metaAddr univs
      | none => do
        let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
        return .const name contAddr metaAddr univs
  | .app fnc arg => return .app (← compileExpr fnc) (← compileExpr arg)
  | .lam name typ bod info =>
    return .lam name info (← compileExpr typ) (← withBinder name $ compileExpr bod)
  | .forallE name dom img info =>
    return .pi name info (← compileExpr dom) (← withBinder name $ compileExpr img)
  | .letE name typ exp bod nD =>
    return .letE name (← compileExpr typ) (← compileExpr exp)
      (← withBinder name $ compileExpr bod) nD
  | .lit lit => return .lit lit
  | .proj name idx exp => do
    let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
    return .proj name contAddr metaAddr idx (← compileExpr exp)
  | .fvar ..  => throw $ .freeVariableExpr expr
  | .mvar ..  => throw $ .metaVariableExpr expr
  | .mdata .. => throw $ .metaDataExpr expr

/--
A name-irrelevant ordering of Lean expressions.
`weakOrd` contains the best known current mutual ordering
-/
partial def compareExpr (weakOrd : RBMap Lean.Name Nat compare)
  : Lean.Expr → Lean.Expr → CompileM Ordering
  | e@(.mvar ..), _ => throw $ .unfilledExprMetavariable e
  | _, e@(.mvar ..) => throw $ .unfilledExprMetavariable e
  | e@(.fvar ..), _ => throw $ .freeVariableExpr e
  | _, e@(.fvar ..) => throw $ .freeVariableExpr e
  | .mdata _ x, .mdata _ y  => compareExpr weakOrd x y
  | .mdata _ x, y  => compareExpr weakOrd x y
  | x, .mdata _ y  => compareExpr weakOrd x y
  | .bvar x, .bvar y => return (compare x y)
  | .bvar .., _ => return .lt
  | _, .bvar .. => return .gt
  | .sort x, .sort y => compareLevel x y
  | .sort .., _ => return .lt
  | _, .sort .. => return .gt
  | .const x xls, .const y yls => do
    let univs ← concatOrds <$> (xls.zip yls).mapM fun (x,y) => compareLevel x y
    if univs != .eq then return univs
    match weakOrd.find? x, weakOrd.find? y with
    | some nx, some ny => return compare nx ny
    | none, some _ => return .gt
    | some _, none => return .lt
    | none, none =>
      return compare
        (← compileConst $ ← findLeanConst x)
        (← compileConst $ ← findLeanConst y)
  | .const .., _ => return .lt
  | _, .const .. => return .gt
  | .app xf xa, .app yf ya =>
    (· * ·) <$> compareExpr weakOrd xf yf <*> compareExpr weakOrd xa ya
  | .app .., _ => return .lt
  | _, .app .. => return .gt
  | .lam _ xt xb _, .lam _ yt yb _ =>
    (· * ·) <$> compareExpr weakOrd xt yt <*> compareExpr weakOrd xb yb
  | .lam .., _ => return .lt
  | _, .lam .. => return .gt
  | .forallE _ xt xb _, .forallE _ yt yb _ =>
    (· * ·) <$> compareExpr weakOrd xt yt <*> compareExpr weakOrd xb yb
  | .forallE .., _ => return .lt
  | _, .forallE .. => return .gt
  | .letE _ xt xv xb _, .letE _ yt yv yb _ =>
    (· * · * ·) <$> compareExpr weakOrd xt yt <*> compareExpr weakOrd xv yv <*> compareExpr weakOrd xb yb
  | .letE .., _ => return .lt
  | _, .letE .. => return .gt
  | .lit x, .lit y =>
    return if x < y then .lt else if x == y then .eq else .gt
  | .lit .., _ => return .lt
  | _, .lit .. => return .gt
  | .proj _ nx tx, .proj _ ny ty => do
    let ts ← compareExpr weakOrd tx ty
    return concatOrds [compare nx ny, ts]

/-- AST comparison of two Lean definitions.
  `weakOrd` contains the best known current mutual ordering -/
partial def compareDef
  (weakOrd : RBMap Lean.Name Nat compare)
  (x : Lean.DefinitionVal) 
  (y : Lean.DefinitionVal) 
  : CompileM Ordering := do
  let ls := compare x.levelParams.length y.levelParams.length
  let ts ← compareExpr weakOrd x.type y.type
  let vs ← compareExpr weakOrd x.value y.value
  return concatOrds [ls, ts, vs]

/-- AST equality between two Lean definitions.
  `weakOrd` contains the best known current mutual ordering -/
@[inline] partial def eqDef
  (weakOrd : RBMap Lean.Name Nat compare)
  (x y : Lean.DefinitionVal) 
  : CompileM Bool :=
  return (← compareDef weakOrd x y) == .eq

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
    CompileM (List (List Lean.DefinitionVal)) := do
  let enum (ll : List (List Lean.DefinitionVal)) :=
    RBMap.ofList (ll.zipIdx.map fun (xs, n) => xs.map (·.name, n)).flatten
  let weakOrd := enum dss _
  let newDss ← (← dss.mapM fun ds =>
    match ds with
    | []  => unreachable!
    | [d] => pure [[d]]
    | ds  => do pure $ (← List.groupByM (eqDef weakOrd) $
      ← ds.sortByM (compareDef weakOrd))).joinM

  -- must normalize, see comments
  let normDss    := dss.map    fun ds => ds.map (·.name) |>.sort
  let normNewDss := newDss.map fun ds => ds.map (·.name) |>.sort
  if normDss == normNewDss then return newDss
  else sortDefs newDss

end

partial def makeLeanDef
  (name: Lean.Name) (levelParams: List Lean.Name) (type value: Lean.Expr) 
  : Lean.DefinitionVal :=
  { name, levelParams, type, value, hints := .opaque, safety := .safe }

partial def tryAddLeanDecl (defn: Lean.DefinitionVal) : CompileM Unit := do
  match (<- get).env.constants.find? defn.name with
  | some _ => pure ()
  | none => do
    let env <- (·.env) <$> get
    let maxHeartBeats <- (·.maxHeartBeats) <$> read
    let decl := Lean.Declaration.defnDecl defn
    match Lean.Environment.addDeclCore env maxHeartBeats decl .none with
    | .ok e => do
      modify fun stt => { stt with env := e }
      return ()
    | .error e => throw $ .kernelException e

partial def addDef (lvls: List Lean.Name) (typ val: Lean.Expr)
  : CompileM (Address × Address) := do
  let typ' <- compileExpr typ
  let val' <- compileExpr val
  let (a, m) <- hashConst $ Ix.Const.definition ⟨lvls, typ', val', true⟩
  tryAddLeanDecl (makeLeanDef a.toUniqueName lvls typ val)
  return (a, m)

partial def commitConst (anon meta: Address)
  : CompileM (Address × Address) := do
  let secret <- freshSecret
  let comm := .comm ⟨secret, anon⟩
  let commAddr <- storeConst comm
  let commMeta := .comm ⟨secret, meta⟩
  let commMetaAddr <- storeConst commMeta
  modify fun stt => { stt with
    comms := stt.comms.insert commAddr.toUniqueName (commAddr, commMetaAddr)
  }
  return (commAddr, commMetaAddr)

partial def commitDef (lvls: List Lean.Name) (typ val: Lean.Expr)
  : CompileM (Address × Address) := do
  let (a, m) <- addDef lvls typ val
  let (ca, cm) <- commitConst a m
  tryAddLeanDecl (makeLeanDef ca.toUniqueName lvls typ val)
  --tryAddLeanDecl (makeLeanDef ca.toUniqueName lvls typ (mkConst a.toUniqueName []))
  return (ca, cm)


partial def packLevel (lvls: Nat) (commit: Bool): CompileM Address :=
  match Ixon.natPackAsAddress lvls with
  | some lvlsAddr => do
    if commit then
      let secret <- freshSecret
      let comm := .comm (Ixon.Comm.mk secret lvlsAddr)
      let commAddr <- storeConst comm
      modify fun stt => { stt with
        comms := stt.comms.insert commAddr.toUniqueName (commAddr, commAddr)
      }
      return commAddr
    else return lvlsAddr
  | .none => throw $ .cantPackLevel lvls

partial def checkClaim
  (const: Lean.Name)
  (type: Lean.Expr)
  (sort: Lean.Expr)
  (lvls: List Lean.Name)
  (commit: Bool)
  : CompileM (Claim × Address × Address) := do
  let leanConst <- findLeanConst const
  let (value, valMeta) <- compileConst leanConst >>= comm
  let (type, typeMeta) <- addDef lvls sort type >>= comm
  let lvls <- packLevel lvls.length commit
  return (Claim.checks lvls type value, typeMeta, valMeta)
  where
    comm a := if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a

partial def evalClaim
  (lvls: List Lean.Name)
  (input: Lean.Expr)
  (output: Lean.Expr)
  (type: Lean.Expr)
  (sort: Lean.Expr)
  (commit: Bool)
  : CompileM (Claim × Address × Address × Address) := do
  let (input, inputMeta) <- addDef lvls type input >>= comm
  let (output, outputMeta) <- addDef lvls type output >>= comm
  let (type, typeMeta) <- addDef lvls sort type >>= comm
  let lvlsAddr <- packLevel lvls.length commit
  return (Claim.evals lvlsAddr input output type, inputMeta, outputMeta, typeMeta)
  where
    comm a := if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a

/--
Content-addresses the "delta" of an environment, that is, the content that is
added on top of the imports.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def compileDelta (delta : Lean.PersistentHashMap Lean.Name Lean.ConstantInfo)
  : CompileM Unit := do
  delta.forM fun _ c => if !c.isUnsafe then discard $ compileConst c else pure ()

def CompileM.runIO (env: Lean.Environment) (c : CompileM α) (maxHeartBeats: USize := 200000)
  : IO (α × CompileState) := do
  match c.run (.init maxHeartBeats) (.init env (<- IO.monoNanosNow)) with
  | .ok a stt => do
    stt.store.forM fun a c => discard $ (Store.forceWriteConst a c).toIO
    return (a, stt)
  | .error e _ => throw (IO.userError (<- e.pretty))

def compileEnvIO (env: Lean.Environment) : IO CompileState := do
  Prod.snd <$> CompileM.runIO env (compileDelta env.getDelta)

