import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.Mutual
import Ix.Common
import Ix.CondenseM
import Ix.GraphM
import Ix.Store
import Ix.SOrder
import Ix.Cronos

namespace Ix
open Ixon hiding Substring

structure CompileEnv where
  env: Lean.Environment
  consts: Map Lean.Name MetaAddress
  comms: Map Lean.Name MetaAddress
  all: Set Lean.Name
  current: Lean.Name
  mutCtx: MutCtx
  univCtx: List Lean.Name

def CompileEnv.init
  (env: Lean.Environment)
  (consts: Map Lean.Name MetaAddress)
  (comms: Map Lean.Name MetaAddress)
  (all: Set Lean.Name)
  (current: Lean.Name)
  : CompileEnv := ⟨env, consts, comms, all, current, default, default⟩

structure CompileState where
  constCache: Map Lean.Name MetaAddress
  univCache: Map Lean.Level MetaAddress
  exprCache: Map Lean.Expr MetaAddress
  synCache: Map Lean.Syntax Ixon.Syntax
  nameCache: Map Lean.Name Address
  strCache: Map String Address
  constCmp: Map (Lean.Name × Lean.Name) Ordering
  blocks: Set MetaAddress
  deriving Inhabited, Nonempty

def CompileState.init : CompileState :=
  ⟨default, default, default, default, default, default, default, default⟩

inductive CompileError where
| unknownConstant (curr unknown: Lean.Name): CompileError
| levelMetavariable : Lean.Level -> CompileError
| exprMetavariable : Lean.Expr -> CompileError
| exprFreeVariable : Lean.Expr -> CompileError
| invalidBVarIndex : Nat -> CompileError
| levelNotFound : Lean.Name -> Lean.Name -> List Lean.Name -> String -> CompileError
| invalidConstantKind : Lean.Name -> String -> String -> CompileError
| mutualBlockMissingProjection : Lean.Name -> CompileError
--| nonRecursorExtractedFromChildren : Lean.Name → CompileError
| cantFindMutIndex : Lean.Name -> MutCtx -> CompileError
| cantFindMutMeta : Lean.Name -> Map Address Address -> CompileError
| kernelException : Lean.Kernel.Exception → CompileError
--| cantPackLevel : Nat → CompileError
--| nonCongruentInductives : PreInd -> PreInd -> CompileError
| alphaInvarianceFailure : Lean.ConstantInfo -> MetaAddress -> Lean.ConstantInfo -> MetaAddress -> CompileError
--| dematBadMutualBlock: MutualBlock -> CompileError
--| dematBadInductiveBlock: InductiveBlock -> CompileError
| badMutualBlock: List (List MutConst) -> CompileError
| badIxonDeserialization : Address -> String -> CompileError
| unknownStoreAddress : Address -> CompileError
| condensationError : Lean.Name -> CompileError
--| emptyIndsEquivalenceClass: List (List PreInd) -> CompileError

def CompileError.pretty : CompileError -> IO String
| .unknownConstant c n => pure s!"Unknown constant '{n}' @ {c}"
| .levelMetavariable l => pure s!"Unfilled level metavariable on universe '{l}'"
| .exprMetavariable e => pure s!"Unfilled level metavariable on expression '{e}'"
| .exprFreeVariable e => pure s!"Free variable in expression '{e}'"
| .invalidBVarIndex idx => pure s!"Invalid index {idx} for bound variable context"
| .levelNotFound c n ns msg => pure s!"'Level {n}' not found in '{ns}', {msg} @ {c}"
| .invalidConstantKind n ex gt => pure s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
| .mutualBlockMissingProjection n => pure s!"Constant '{n}' wasn't content-addressed in mutual block"
| .cantFindMutIndex n mc => pure s!"Can't find index for mutual definition '{n}' in {repr mc}"
| .cantFindMutMeta n ms => pure s!"Can't find metadata for mutual definition
'{n}' in {repr ms}"
| .kernelException e => (·.pretty 80) <$> (e.toMessageData .empty).format
| .alphaInvarianceFailure x xa y ya =>
  pure s!"alpha invariance failure {repr x} hashes to {xa}, but {repr y} hashes to {ya}"
| .badMutualBlock block => pure s!"bad mutual block {repr block}"
| .badIxonDeserialization a s => pure s!"bad deserialization of ixon at {a}, error: {s}"
| .unknownStoreAddress a => pure s!"unknown store address {a}"
| .condensationError n => pure s!"condensation error {n}"

abbrev CompileM :=
  ReaderT CompileEnv <| ExceptT CompileError <| StateT CompileState IO

abbrev CompileM.Result α := (Except CompileError α × CompileState)

def CompileM.run (env: CompileEnv) (stt: CompileState) (c : CompileM α)
  : IO (Except CompileError α × CompileState)
  := StateT.run (ExceptT.run (ReaderT.run c env)) stt

--def randByte (lo hi: Nat): CompileM Nat := do
--  modifyGet fun s =>
--  let (res, g') := randNat s.prng lo hi
--  (res, {s with prng := g'})
--
--def freshSecret : CompileM Address := do
--  let mut secret: ByteArray := default
--  for _ in [:32] do
--    let rand <- randByte 0 255
--    secret := secret.push rand.toUInt8
--  return ⟨secret⟩


-- add binding name to local context
def CompileM.withCurrent (name: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with current := name }

-- add levels to local context
def CompileM.withLevels (lvls : List Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def CompileM.withMutCtx (mutCtx : MutCtx) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

-- reset local context
def CompileM.resetCtx (current: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := [], mutCtx := {}, current }

def storeIxon (ixon: Ixon): CompileM Address := do
  liftM (Store.write (Ixon.ser ixon)).toIO

def storeString (str: String): CompileM Address := do
  match (<- get).strCache.find? str with
  | some addr => pure addr
  | none =>
  liftM (Store.write (str.toUTF8)).toIO

def storeNat (nat: Nat): CompileM Address := do
  liftM (Store.write (⟨nat.toBytesLE⟩)).toIO

def storeSerial [Serialize A] (a: A): CompileM Address := do
  liftM (Store.write (Ixon.ser a)).toIO

def storeMeta (met: Metadata): CompileM Address := do
  liftM (Store.write (Ixon.ser met)).toIO

def compileName (name: Lean.Name): CompileM Address := do
  match (<- get).nameCache.find? name with
  | some addr =>
    --dbg_trace "compileName cached {(<- read).current} {name}"
    pure addr
  | none => do
    --dbg_trace "compileName {(<- read).current} {name}"
    let addr <- go name
    modifyGet fun stt => (addr, { stt with
      nameCache := stt.nameCache.insert name addr
    })
  where
    go : Lean.Name -> CompileM Address
    | .anonymous => storeIxon .nanon
    | .str n s => do
      let n' <- compileName n
      let s' <- storeString s
      storeIxon (.nstr n' s')
    | .num n i => do
      let n' <- compileName n
      let i' <- storeNat i
      storeIxon (.nnum n' i')

/-- Defines an ordering for Lean universes -/
def compareLevel (xctx yctx: List Lean.Name)
  : Lean.Level -> Lean.Level -> CompileM SOrder
  | x@(.mvar ..), _ => throw $ .levelMetavariable x
  | _, y@(.mvar ..) => throw $ .levelMetavariable y
  | .zero, .zero => return ⟨true, .eq⟩
  | .zero, _ => return ⟨true, .lt⟩
  | _, .zero => return ⟨true, .gt⟩
  | .succ x, .succ y => compareLevel xctx yctx x y
  | .succ .., _ => return ⟨true, .lt⟩
  | _, .succ .. => return ⟨true, .gt⟩
  | .max xl xr, .max yl yr => SOrder.cmpM
    (compareLevel xctx yctx xl yl) (compareLevel xctx yctx xr yr)
  | .max .., _ => return ⟨true, .lt⟩
  | _, .max .. => return ⟨true, .gt⟩
  | .imax xl xr, .imax yl yr => SOrder.cmpM
      (compareLevel xctx yctx xl yl) (compareLevel xctx yctx xr yr)
  | .imax .., _ => return ⟨true, .lt⟩
  | _, .imax .. => return ⟨true, .gt⟩
  | .param x, .param y => do
    match (xctx.idxOf? x), (yctx.idxOf? y) with
    | some xi, some yi => return ⟨true, compare xi yi⟩
    | none,    _       =>
      throw $ .levelNotFound (<- read).current x xctx s!"compareLevel"
    | _,       none    =>
      throw $ .levelNotFound (<- read).current y yctx s!"compareLevel"

/-- Canonicalizes a Lean universe level --/
def compileLevel (lvl: Lean.Level): CompileM MetaAddress := do
  match (<- get).univCache.find? lvl with
  | some l =>
    --dbg_trace "compileLevel cached {(<- get).univCache.size} {(<- read).current}"
    pure l
  | none => do
    --dbg_trace "compileLevel {(<- get).univCache.size} {(<- read).current}"
    let (dat, met) <- go lvl
    let maddr := ⟨<- storeIxon dat, <- storeIxon met⟩
    modifyGet fun stt => (maddr, { stt with
      univCache := stt.univCache.insert lvl maddr
    })
  where
    go : Lean.Level -> CompileM (Ixon × Ixon)
    | .zero => pure (.uzero, .meta default)
    | .succ x => do
      let ⟨a, m⟩ <- compileLevel x
      pure (.usucc a, .meta ⟨[.link m]⟩)
    | .max x y => do
      let ⟨xa, xm⟩ <- compileLevel x
      let ⟨ya, ym⟩ <- compileLevel y
      pure (.umax xa ya, .meta ⟨[.link xm, .link ym]⟩)
    | .imax x y => do
      let ⟨xa, xm⟩ <- compileLevel x
      let ⟨ya, ym⟩ <- compileLevel y
      pure (.uimax xa ya, .meta ⟨[.link xm, .link ym]⟩)
    | .param n => do
      let lvls := (← read).univCtx
      match lvls.idxOf? n with
      | some i => pure (.uvar i, .meta ⟨[.link (<- compileName n)]⟩)
      | none   => do throw <| .levelNotFound (<- read).current n lvls s!"compileLevel"
    | l@(.mvar ..) => throw $ .levelMetavariable l

def compileSubstring : Substring -> CompileM Ixon.Substring
| ⟨str, startPos, stopPos⟩ => do
    pure ⟨<- storeString str, startPos.byteIdx, stopPos.byteIdx⟩

def compileSourceInfo : Lean.SourceInfo -> CompileM Ixon.SourceInfo
| .original l p t e => do
  let l' <- compileSubstring l
  let t' <- compileSubstring t
  pure <| .original l' p.byteIdx t' e.byteIdx
| .synthetic p e c => pure (.synthetic p.byteIdx e.byteIdx c)
| .none => pure .none

def compilePreresolved : Lean.Syntax.Preresolved -> CompileM Ixon.Preresolved
| .namespace ns => .namespace <$> compileName ns
| .decl n fs => .decl <$> compileName n <*> fs.mapM storeString

partial def compileSyntax (syn: Lean.Syntax) : CompileM Ixon.Syntax := do
  --dbg_trace "compileSyntax {(<- read).current}"
  match (<- get).synCache.find? syn with
  | some x => pure x
  | none => do
    let syn' <- go syn
    modifyGet fun stt => (syn', { stt with
      synCache := stt.synCache.insert syn syn'
    })
  where
    go : Lean.Syntax -> CompileM Ixon.Syntax
    | .missing => pure .missing
    | .node info kind args => do
      let info' <- compileSourceInfo info
      let kind' <- compileName kind
      let args' <- args.toList.mapM (compileSyntax · >>= storeSerial)
      pure <| .node info' kind' args'
    | .atom info val => do
      let info' <- compileSourceInfo info
      let val' <- storeString val
      pure <| .atom info' val'
    | .ident info rawVal val preresolved => do
      let info' <- compileSourceInfo info
      let rawVal' <- compileSubstring rawVal
      let val' <- compileName val
      let ps' <- preresolved.mapM compilePreresolved
      pure <| .ident info' rawVal' val' ps'

def compileDataValue : Lean.DataValue -> CompileM Ixon.DataValue
| .ofString s => .ofString <$> storeString s
| .ofBool b => pure (.ofBool b)
| .ofName n => .ofName <$> compileName n
| .ofNat i => .ofNat <$> storeNat i
| .ofInt i => .ofInt <$> storeSerial i
| .ofSyntax s => .ofSyntax <$> (compileSyntax s >>= storeSerial)

def compileKVMap (map: Lean.KVMap): CompileM Address := do
  let mut list := #[]
  for (name, dataValue) in map do
    let n <- compileName name
    let d <- compileDataValue dataValue
    list := list.push (n, d)
  storeIxon (.meta ⟨[.kvmap list.toList]⟩)

def findLeanConst (name : Lean.Name) : CompileM Lean.ConstantInfo := do
  match (<- read).env.constants.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant (<- read).current name

def MutConst.mkIndc (i: Lean.InductiveVal) : CompileM MutConst := do
  let ctors <- i.ctors.mapM getCtor
  return .indc ⟨i.name, i.levelParams, i.type, i.numParams, i.numIndices, i.all,
    ctors, i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩
  where
    getCtor (name: Lean.Name) : CompileM (Lean.ConstructorVal) := do
      match (<- findLeanConst name) with
      | .ctorInfo c => pure c
      | _ => throw <| .invalidConstantKind name "constructor" ""

def compileReference (name: Lean.Name): CompileM MetaAddress := do
  if name == Lean.Name.mkSimple "_obj" then
    return ⟨<- storeIxon <| .prim .obj, <- storeIxon <| .meta ⟨[]⟩⟩
  else if name == Lean.Name.mkSimple "_neutral" then
    return ⟨<- storeIxon <| .prim .neutral, <- storeIxon <| .meta ⟨[]⟩⟩
  else if name == Lean.Name.mkSimple "_unreachable" then
    return ⟨<- storeIxon <| .prim .unreachable, <- storeIxon <| .meta ⟨[]⟩⟩
  else match (<- read).comms.find? name with
    | some comm => pure comm
    | none => match (<- read).consts.find? name with
      | some ref => pure ref
      | none => do throw <| .unknownConstant (<- read).current name

def compileExpr: Lean.Expr -> CompileM MetaAddress
| expr => do match (<- get).exprCache.find? expr with
  | some x => pure x
  | none => do
    --dbg_trace s!"compileExpr {(<- read).current} {(<- get).exprCache.size}"
    let maddr <- go expr
    modifyGet fun stt => (maddr, { stt with
      exprCache := stt.exprCache.insert expr maddr
    })
  where
    go: Lean.Expr -> CompileM MetaAddress
    | (.mdata kv x) => do
      let md <- compileKVMap kv
      let x <- compileExpr x
      return ⟨x.data, <- storeIxon (.meta ⟨[.link md, .link x.meta]⟩)⟩
    | .bvar idx => do
      --dbg_trace s!"compileExpr {(<- read).current} bvar"
      let dat := .evar idx
      let met  := .meta ⟨[]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .sort univ => do
      --dbg_trace s!"compileExpr {(<- read).current} sort"
      let ⟨udata, umeta⟩ <- compileLevel univ
      let dat := .esort udata
      let met := .meta ⟨[.link umeta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .const name lvls => do
      --dbg_trace s!"compileExpr {(<- read).current} const"
      let n <- compileName name
      let us <- lvls.mapM compileLevel
      match (← read).mutCtx.find? name with
      | some idx =>
        --dbg_trace s!"compileExpr {(<- read).current} const rec"
        let dat := .erec idx (us.map (·.data))
        let met := .meta ⟨[.link n, .links (us.map (·.meta))]⟩
        pure ⟨<- storeIxon dat, <- storeIxon met⟩
      | none => do
        let ref <- compileReference name
        --dbg_trace s!"compileExpr {(<- read).current}, const ref {name}, mutCtx: {repr (<- read).mutCtx}"
        let dat := .eref ref.data (us.map (·.data))
        let met := .meta ⟨[.link n, .link ref.meta, .links (us.map (·.meta))]⟩
        pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .app func argm => do
      --dbg_trace s!"compileExpr {(<- read).current} app"
      let f <- compileExpr func
      let a <- compileExpr argm
      let dat := .eapp f.data a.data
      let met := .meta ⟨[.link f.meta, .link a.meta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .lam name type body info => do
      --dbg_trace s!"compileExpr {(<- read).current} lam"
      let n <- compileName name
      let t <- compileExpr type
      let b <- compileExpr body
      let dat := .elam t.data b.data
      let met := .meta ⟨[.link n, .info info, .link t.meta, .link b.meta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .forallE name type body info => do
      --dbg_trace s!"compileExpr {(<- read).current} all"
      --dbg_trace s!"compileExpr {(<- read).current} all md"
      let n <- compileName name
      --dbg_trace s!"compileExpr {(<- read).current} all n"
      let t <- compileExpr type
      --dbg_trace s!"compileExpr {(<- read).current} all t"
      let b <- compileExpr body
      --dbg_trace s!"compileExpr {(<- read).current} all b"
      let dat := .eall t.data b.data
      let met := .meta ⟨[.link n, .info info, .link t.meta, .link b.meta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .letE name type value body nD => do
      --dbg_trace s!"compileExpr {(<- read).current} let"
      let n <- compileName name
      let t <- compileExpr type
      let v <- compileExpr value
      let b <- compileExpr body
      let dat:= .elet nD t.data v.data b.data
      let met := .meta ⟨[.link n, .link t.meta, .link v.meta, .link b.meta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .lit (.natVal n) => do
      let dat := .enat (<- storeNat n)
      let met := .meta ⟨[]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .lit (.strVal s) => do
      --dbg_trace s!"compileExpr {(<- read).current} lit str"
      let dat := .estr (<- storeString s)
      let met := .meta ⟨[]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | .proj typeName idx struct => do
      --dbg_trace s!"compileExpr {(<- read).current} lit proj"
      let t <- compileReference typeName
      let n <- compileName typeName
      let s <- compileExpr struct
      let dat := .eprj t.data idx s.data
      let met := .meta ⟨[.link n, .link t.meta, .link s.meta]⟩
      pure ⟨<- storeIxon dat, <- storeIxon met⟩
    | expr@(.fvar ..)  => throw $ .exprFreeVariable expr
    | expr@(.mvar ..)  => throw $ .exprMetavariable expr

def compileDefn: Ix.Def -> CompileM (Ixon.Definition × Ixon.Metadata)
| d => .withLevels d.levelParams do
  --dbg_trace "compileDefn"
  let n <- compileName d.name
  let ls <- d.levelParams.mapM compileName
  let t <- compileExpr d.type
  let v <- compileExpr d.value
  let as <- d.all.mapM compileName
  let dat := ⟨d.kind, d.safety, ls.length, t.data, v.data⟩
  let met := ⟨[.link n, .links ls, .hints d.hints, .link t.meta, .link v.meta, .links as]⟩
  return (dat, met)

partial def compileRule: Lean.RecursorRule -> CompileM (Ixon.RecursorRule × Address × Address)
| r => do
  --dbg_trace "compileRule"
  let n <- compileName r.ctor
  let rhs <- compileExpr r.rhs
  pure (⟨r.nfields, rhs.data⟩, (n, rhs.meta))

def compileRecr: Lean.RecursorVal -> CompileM (Ixon.Recursor × Metadata)
| r => .withLevels r.levelParams <| do
  --dbg_trace s!"compileRecr {(<- read).current} {repr <| r.name} mutCtx: {repr (<- read).mutCtx}"
  let n <- compileName r.name
  let ls <- r.levelParams.mapM compileName
  let t <- compileExpr r.type
  let rules <- r.rules.mapM compileRule
  let as <- r.all.mapM compileName
  let dat := ⟨r.k, r.isUnsafe, ls.length, r.numParams, r.numIndices,
    r.numMotives, r.numMinors, t.data, rules.map (·.1)⟩
  let met := ⟨[.link n, .links ls, .link t.meta, .map (rules.map (·.2)), .links as]⟩
  pure (dat, met)

def compileConstructor (induct: Address)
: Lean.ConstructorVal -> CompileM (Ixon.Constructor × Metadata)
| c => .withLevels c.levelParams <| do
  --dbg_trace s!"compileCtor {(<- read).current} {repr <| c.name} mutCtx: {repr (<- read).mutCtx}"
  let n <- compileName c.name
  let ls <- c.levelParams.mapM compileName
  let t <- compileExpr c.type
  let dat := ⟨c.isUnsafe, ls.length, c.cidx, c.numParams, c.numFields, t.data⟩
  let met := ⟨[.link n, .links ls, .link t.meta, .link induct]⟩
  pure (dat, met)

partial def compileIndc: Ix.Ind -> CompileM (Ixon.Inductive × Map Address Address)
| ⟨name, lvls, type, ps, is, all, ctors, nest, rcr, refl, usafe⟩ =>
  .withLevels lvls do
  --dbg_trace s!"compileIndc {(<- read).current} {repr <| name} mutCtx: {repr (<- read).mutCtx}"
  let n <- compileName name
  let ls <- lvls.mapM compileName
  let t <- compileExpr type
  let mut cds := #[]
  let mut cms := #[]
  let mut metaMap := {}
  for ctor in ctors do
    let (cd, cm) <- compileConstructor n ctor
    let cn <- compileName ctor.name
    cds := cds.push cd
    let cm' <- storeMeta cm
    cms := cms.push cm'
    metaMap := metaMap.insert cn cm'
  let as <- all.mapM compileName
  let data := ⟨rcr, refl, usafe, ls.length, ps, is, nest, t.data, cds.toList⟩
  let «meta» := ⟨[.link n, .links ls, .link t.meta, .links cms.toList, .links as]⟩
  let m <- storeMeta «meta»
  metaMap := metaMap.insert n m
  pure (data, metaMap)

/-- A name-irrelevant ordering of Lean expressions --/
def compareExpr (ctx: MutCtx) (xlvls ylvls: List Lean.Name)
  (x y: Lean.Expr): CompileM SOrder := do
  --dbg_trace "compareExpr"
  match x, y with
  | e@(.mvar ..), _ => throw $ .exprMetavariable e
  | _, e@(.mvar ..) => throw $ .exprMetavariable e
  | e@(.fvar ..), _ => throw $ .exprFreeVariable e
  | _, e@(.fvar ..) => throw $ .exprFreeVariable e
  | .mdata _ x, .mdata _ y  => compareExpr ctx xlvls ylvls x y
  | .mdata _ x, y  => compareExpr ctx xlvls ylvls x y
  | x, .mdata _ y  => compareExpr ctx xlvls ylvls x y
  | .bvar x, .bvar y => return ⟨true, compare x y⟩
  | .bvar .., _ => return ⟨true, .lt⟩
  | _, .bvar .. => return ⟨true, .gt⟩
  | .sort x, .sort y => compareLevel xlvls ylvls x y
  | .sort .., _ => return ⟨true, .lt⟩
  | _, .sort .. => return ⟨true, .gt⟩
  | .const x xls, .const y yls => do
    let univs ← SOrder.zipM (compareLevel xlvls ylvls) xls yls
    if univs.ord != .eq then return univs
    if x == y then return ⟨true, .eq⟩
    else match ctx.find? x, ctx.find? y with
    | some nx, some ny => return ⟨false, compare nx ny⟩
    | some _, none => return ⟨true, .lt⟩
    | none, some _ => return ⟨true, .gt⟩
    | none, none => do
      --dbg_trace s!"compareExpr const {(<- read).current} consts {x} {y}"
      let x' <- compileReference x
      let y' <- compileReference y
      return ⟨true, compare x'.data y'.data⟩
  | .const .., _ => return ⟨true, .lt⟩
  | _, .const .. => return ⟨true, .gt⟩
  | .app xf xa, .app yf ya =>
    SOrder.cmpM
      (compareExpr ctx xlvls ylvls xf yf)
      (compareExpr ctx xlvls ylvls xa ya)
  | .app .., _ => return ⟨true, .lt⟩
  | _, .app .. => return ⟨true, .gt⟩
  | .lam _ xt xb _, .lam _ yt yb _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
  | .lam .., _ => return ⟨true, .lt⟩
  | _, .lam .. => return ⟨true, .gt⟩
  | .forallE _ xt xb _, .forallE _ yt yb _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
  | .forallE .., _ => return ⟨true, .lt⟩
  | _, .forallE .. => return ⟨true, .gt⟩
  | .letE _ xt xv xb _, .letE _ yt yv yb _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) <|
    SOrder.cmpM (compareExpr ctx xlvls ylvls xv yv)
      (compareExpr ctx xlvls ylvls xb yb)
  | .letE .., _ => return ⟨true, .lt⟩
  | _, .letE .. => return ⟨true, .gt⟩
  | .lit x, .lit y => return ⟨true, compare x y⟩
  | .lit .., _ => return ⟨true, .lt⟩
  | _, .lit .. => return ⟨true, .gt⟩
  | .proj tnx ix tx, .proj tny iy ty => do
    let tn <- match ctx.find? tnx, ctx.find? tny with
      | some nx, some ny => pure ⟨false, compare nx ny⟩
      | none, some _ => pure ⟨true, .gt⟩
      | some _, none => pure ⟨true, .lt⟩
      | none, none =>
        if tnx == tny then pure ⟨true, .eq⟩
        else do
          let x' <- compileReference tnx
          let y' <- compileReference tny
          pure ⟨true, compare x' y'⟩
    SOrder.cmpM (pure tn) <|
    SOrder.cmpM (pure ⟨true, compare ix iy⟩) <|
    (compareExpr ctx xlvls ylvls tx ty) 

/-- ast comparison of two lean definitions. --/
def compareConst (ctx: MutCtx) (x y: MutConst)
  : CompileM Ordering := do
  --dbg_trace "compareConst"
  let key := match compare x.name y.name with
    | .lt => (x.name, y.name)
    | _ => (y.name, x.name)
  match (<- get).constCmp.find? key with
  | some o => return o
  | none => do
    let sorder: SOrder <- match x,y with
    | .defn x, .defn y => compareDef x y
    | .defn _, _ => pure ⟨true, Ordering.lt⟩
    | .indc x, .indc y => compareInd x y
    | .indc _, _ => pure ⟨true, Ordering.lt⟩
    | .recr x, .recr y => compareRecr x y
    | .recr _, _ => pure ⟨true, Ordering.lt⟩
    if sorder.strong then modify fun stt => { stt with
        constCmp := stt.constCmp.insert key sorder.ord
      }
    return sorder.ord
  where
    compareDef (x y: Def) : CompileM SOrder := do
      SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type)
        (compareExpr ctx x.levelParams y.levelParams x.value y.value)
    compareInd (x y: Ind) : CompileM SOrder := do
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.ctors.length y.ctors.length⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
      (SOrder.zipM compareCtor x.ctors y.ctors)
    compareCtor (x y: Lean.ConstructorVal) : CompileM SOrder := do
      let key := match compare x.name y.name with
        | .lt => (x.name, y.name)
        | _ => (y.name, x.name)
      match (<- get).constCmp.find? key with
      | some o => return ⟨true, o⟩
      | none => do
      let sorder <- do
        SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
        SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
        SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
        SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩) <|
          (compareExpr ctx x.levelParams y.levelParams x.type y.type)
      if sorder.strong then modify fun stt => { stt with
          constCmp := stt.constCmp.insert key sorder.ord
        }
      return sorder
    compareRecr (x y: Lean.RecursorVal) : CompileM SOrder := do
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numParams y.numParams⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numIndices y.numIndices⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numMotives y.numMotives⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numMinors y.numMinors⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.k y.k⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
        (SOrder.zipM (compareRule x.levelParams y.levelParams) x.rules y.rules)
    compareRule (xlvls ylvls: List Lean.Name) (x y: Lean.RecursorRule)
      : CompileM SOrder := do
        SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩)
          (compareExpr ctx xlvls ylvls x.rhs y.rhs)

def eqConst (ctx: MutCtx) (x y: MutConst) : CompileM Bool :=
  (fun o => o == .eq) <$> compareConst ctx x y

/-- `sortConsts` recursively sorts a list of mutually referential constants into
ordered equivalence classes. For most cases equivalence can be determined by
syntactic differences in the definitions, but when two definitions
refer to one another in the same syntactical position the classification can
be self-referential. Therefore we use a partition refinement algorithm that
starts by assuming that all definitions in the mutual block are equal and
recursively improves our classification by sorting based on syntax:
```
classes₀ := [startConsts]
classes₁ := sortConsts classes₀
classes₂ := sortConsts classes₁
classes₍ᵢ₊₁₎ := sortConsts classesᵢ ...
```
Eventually we reach a fixed-point where `classes₍ᵢ₊₁₎ := classesᵢ` and no
further refinement is possible (trivially when each const is in its own class). --/
partial def sortConsts (classes: List MutConst) : CompileM (List (List MutConst))
  := go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List MutConst)): CompileM (List (List MutConst)) := do
    --dbg_trace "sortConsts {(<- read).current} {cs.map (·.map (·.name))}"
      let ctx := MutConst.ctx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .badMutualBlock cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareConst ctx) >>= List.groupByM (eqConst ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'

/-- Compile a mutual block --/
partial def compileMutConsts: List (List MutConst)
  -> CompileM (Ixon × Map Address Address)
| classes => do
  --dbg_trace s!"compileMutConsts {(<- read).current} {repr <| classes.map (·.map (·.name))} mutCtx: {repr (<- read).mutCtx}"
  let mut dat := #[]
  let mut met := {}
  -- iterate through each equivalence class
  for constClass in classes do
    let mut classData := #[]
    -- compile each constant in a class
    for const in constClass do
      match const with
      | .indc x => do
        let (i, m) <- .withCurrent x.name <| compileIndc x
        classData := classData.push (.indc i)
        met := met.union m
      | .defn x => do
        let (d, m) <- .withCurrent x.name <| compileDefn x
        classData := classData.push (.defn d)
        met := met.insert (<- compileName x.name) (<- storeMeta m)
      | .recr x => do
        let (r, m) <- .withCurrent x.name <| compileRecr x
        classData := classData.push (.recr r)
        met := met.insert (<- compileName x.name) (<- storeMeta m)
    -- make sure we have no empty classes and all defs in a class are equal
    match classData.toList with
      | [] => throw (.badMutualBlock classes)
      | [x] => dat := dat.push x
      | x::xs =>
        if xs.foldr (fun y acc => (y == x) && acc) true
        then dat := dat.push x
        else throw (.badMutualBlock classes)
  pure (.muts dat.toList, met)

def compileMutual : MutConst -> CompileM (Ixon × Ixon)
| const => do
  --dbg_trace s!"compileMutual {const.name}"
  let all := (<- read).all
--dbg_trace s!"compileMutual {const.name} all: {repr all}"
  if all == {const.name} &&
    (const matches .defn _ || const matches .recr _) then do
    match const with
    | .defn d => do
      let (dat, met) <- .withMutCtx (.single d.name 0) <| compileDefn d
      pure (.defn dat, .meta met)
    | .recr r => do
      let (dat, met) <- .withMutCtx (.single r.name 0) <| compileRecr r
      pure (.recr dat, .meta met)
    | _ => unreachable!
  else
    let mut consts := #[]
    for name in all do
      match <- findLeanConst name with
      | .inductInfo val => do consts := consts.push (<- MutConst.mkIndc val)
      | .defnInfo val => consts := consts.push (MutConst.mkDefn val)
      | .opaqueInfo val => consts := consts.push (MutConst.mkOpaq val)
      | .thmInfo val => consts := consts.push (MutConst.mkTheo val)
      | .recInfo val => consts := consts.push (MutConst.recr val)
      | _ => continue
    --dbg_trace s!"compileMutual {const.name} consts: {repr <| consts.map (·.name)}"
    -- sort MutConsts into equivalence classes
    let mutConsts <- sortConsts consts.toList
    --dbg_trace s!"compileMutual {const.name} mutConsts: {repr <| mutConsts.map (·.map (·.name))}"
    let mutCtx := MutConst.ctx mutConsts
    --dbg_trace s!"compileMutual {const.name} mutCtx: {repr mutCtx}"
    let mutMeta <- mutConsts.mapM fun m => m.mapM <| fun c => compileName c.name
    -- compile each constant with the mutCtx
    let (data, metas) <- .withMutCtx mutCtx (compileMutConsts mutConsts)
    -- add top-level mutual block to our state
    let ctx <- mutCtx.toList.mapM fun (n, i) => do
      pure (<- compileName n, <- storeNat i)
    let block: MetaAddress :=
      ⟨<- storeIxon data, <- storeMeta ⟨[.muts mutMeta, .map ctx, .map metas.toList]⟩⟩
    modify fun stt => { stt with blocks := stt.blocks.insert block }
    -- then add all projections, returning the inductive we started with
    let mut ret? : Option (Ixon × Ixon) := none
    for const' in consts do
      let idx <- do match mutCtx.find? const'.name with
      | some idx => pure idx
      | none => throw $ .cantFindMutIndex const'.name mutCtx
      let n <- compileName const'.name
      let «meta» <- do match metas.find? n with
      | some «meta» => pure ⟨[.link block.meta, .link «meta»]⟩
      | none => throw $ .cantFindMutMeta const'.name metas
      let data := match const with
      | .defn _ => .dprj ⟨idx, block.data⟩
      | .indc _ => .iprj ⟨idx, block.data⟩
      | .recr _ => .rprj ⟨idx, block.data⟩
      let addr := ⟨<- storeIxon data, <- storeMeta «meta»⟩
      modify fun stt => { stt with
        constCache := stt.constCache.insert const'.name addr
      }
      if const'.name == const.name then ret? := some (data, .meta «meta»)
      for ctor in const'.ctors do
        let cdata := .cprj ⟨idx, ctor.cidx, block.data⟩
        let cn <- compileName ctor.name
        let cmeta <- do match metas.find? cn with
        | some «meta» => pure ⟨[.link block.meta, .link «meta»]⟩
        | none => throw $ .cantFindMutMeta const'.name metas
        let caddr := ⟨<- storeIxon cdata, <- storeMeta cmeta⟩
        modify fun stt => { stt with
          constCache := stt.constCache.insert ctor.name caddr
        }
    match ret? with
    | some ret => return ret
    | none => throw $ .mutualBlockMissingProjection const.name


def compileConstant (name: Lean.Name): CompileM MetaAddress := do
  --dbg_trace "compileConstant {name}"
  match (<- get).constCache.find? name with
  | some x => pure x
  | none => do
    let c <- findLeanConst name
    let maddr <- .withCurrent name <| go c
    modifyGet fun stt => (maddr, { stt with
      constCache := stt.constCache.insert name maddr
    })
  where
    store: Ixon × Ixon -> CompileM MetaAddress
    | (d, m) => do pure ⟨<- storeIxon d, <- storeIxon m⟩
    go : Lean.ConstantInfo -> CompileM MetaAddress
    | .defnInfo val => compileMutual (MutConst.mkDefn val) >>= store
    | .thmInfo val => compileMutual (MutConst.mkTheo val) >>= store
    | .opaqueInfo val => compileMutual (MutConst.mkOpaq val) >>= store
    | .inductInfo val => MutConst.mkIndc val >>= compileMutual >>= store
    | .ctorInfo val => do match <- findLeanConst val.induct with
      | .inductInfo ind => do
        let _ <- MutConst.mkIndc ind >>= compileMutual
        match (<- get).constCache.find? val.name with
        | some maddr => do pure maddr
        | none => throw <| .mutualBlockMissingProjection val.name
      | c => throw <| .invalidConstantKind c.name "inductive" c.ctorName
    | .recInfo val => compileMutual (MutConst.recr val) >>= store
    | .axiomInfo ⟨⟨name, lvls, type⟩, isUnsafe⟩ => .withLevels lvls do
      let n <- compileName name
      let ls <- lvls.mapM compileName
      let t <- compileExpr type
      let dat := .axio ⟨isUnsafe, lvls.length, t.data⟩
      let met := .meta ⟨[.link n, .links ls, .link t.meta]⟩
      store (dat, met)
    | .quotInfo ⟨⟨name, lvls, type⟩, kind⟩ => .withLevels lvls do
      let n <- compileName name
      let ls <- lvls.mapM compileName
      let t <- compileExpr type
      let dat := .quot ⟨kind, lvls.length, t.data⟩
      let met := .meta ⟨[.link n, .links ls, .link t.meta]⟩
      store (dat, met)

--partial def makeLeanDef
--  (name: Lean.Name) (levelParams: List Lean.Name) (type value: Lean.Expr)
--  : Lean.DefinitionVal :=
--  { name, levelParams, type, value, hints := .opaque, safety := .safe }
--
--partial def tryAddLeanDef (defn: Lean.DefinitionVal) : CompileM Unit := do
--  match (<- get).env.constants.find? defn.name with
--  | some _ => pure ()
--  | none => do
--    let env <- (·.env) <$> get
--    let maxHeartBeats <- (·.maxHeartBeats) <$> get
--    let decl := Lean.Declaration.defnDecl defn
--    match Lean.Environment.addDeclCore env maxHeartBeats decl .none with
--    | .ok e => do
--      modify fun stt => { stt with env := e }
--      return ()
--    | .error e => throw $ .kernelException e
--
--partial def addDef (lvls: List Lean.Name) (typ val: Lean.Expr) : CompileM MetaAddress := do
--  --let typ' <- compileExpr typ
--  --let val' <- compileExpr val
--  let anon := .defnInfo ⟨⟨.anonymous, lvls, typ⟩, val, .opaque, .safe, []⟩
--  let (data, «meta») <- compileConstant anon
--  let anonAddr := ⟨<- storeIxon data, <- storeIxon «meta»⟩
--  let name := anonAddr.data.toUniqueName
--  let const := .defnInfo ⟨⟨name, lvls, typ⟩, val, .opaque, .safe, []⟩
--  let (data, «meta») <- compileConstant const
--  let addr := ⟨<- storeIxon data, <- storeIxon «meta»⟩
--  if addr.data != anonAddr.data then
--    throw <| .alphaInvarianceFailure anon anonAddr const addr
--  else
--    tryAddLeanDef (makeLeanDef name lvls typ val)
--    return addr
--
--partial def commitConst (addr: MetaAddress) (secret: Address) : CompileM MetaAddress := do
--  let comm := Ixon.comm ⟨secret, addr.data⟩
--  let commAddr <- storeIxon comm
--  let commMeta := Ixon.comm ⟨secret, addr.meta⟩
--  let commMetaAddr <- storeIxon commMeta
--  let addr' := ⟨commAddr, commMetaAddr⟩
--  modify fun stt => { stt with
--    comms := stt.comms.insert commAddr.toUniqueName addr'
--  }
--  return addr'
--
--partial def commitDef (lvls: List Lean.Name) (typ val: Lean.Expr) (secret: Address): CompileM MetaAddress := do
--  let addr <- addDef lvls typ val
--  let addr' <- commitConst addr secret
--  tryAddLeanDef (makeLeanDef addr'.data.toUniqueName lvls typ val)
--  --tryAddLeanDecl (makeLeanDef ca.toUniqueName lvls typ (mkConst a.toUniqueName []))
--  return addr'
--
--partial def storeLevel (lvls: Nat) (secret: Option Address): CompileM Address := do
--  let addr <- storeNat lvls
--  match secret with
--  | some secret => do
--    let comm := .comm ⟨secret, addr⟩
--    let commAddr <- storeIxon comm
--    modify fun stt => { stt with
--      comms := stt.comms.insert commAddr.toUniqueName ⟨commAddr, commAddr⟩
--    }
--    return commAddr
--  | none => return addr
--
--partial def checkClaim
--  (const: Lean.Name)
--  (type: Lean.Expr)
--  (sort: Lean.Expr)
--  (lvls: List Lean.Name)
--  (secret: Option Address)
--  : CompileM (Claim × Address × Address) := do
--  let leanConst <- findLeanConst const
--  let valAddr <- compileConst leanConst >>= comm
--  let typeAddr <- addDef lvls sort type >>= comm
--  let lvls <- packLevel lvls.length commit
--  return (Claim.checks (CheckClaim.mk lvls type value), typeMeta, valMeta)
--  where
--    commit (c: Ix.Const) : MetaAddress := do
--      match commit with
--      | none => dematerializeConst c
--      | some secret =>
--
--    if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a

--
--partial def evalClaim
--  (lvls: List Lean.Name)
--  (input: Lean.Expr)
--  (output: Lean.Expr)
--  (type: Lean.Expr)
--  (sort: Lean.Expr)
--  (commit: Bool)
--  : CompileM (Claim × Address × Address × Address) := do
--  let (input, inputMeta) <- addDef lvls type input >>= comm
--  let (output, outputMeta) <- addDef lvls type output >>= comm
--  let (type, typeMeta) <- addDef lvls sort type >>= comm
--  let lvlsAddr <- packLevel lvls.length commit
--  return (Claim.evals (EvalClaim.mk lvlsAddr input output type), inputMeta, outputMeta, typeMeta)
--  where
--    comm a := if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a

--/--
--Content-addresses the "delta" of an environment, that is, the content that is
--added on top of the imports.
--
--Important: constants with open references in their expressions are filtered out.
--Open references are variables that point to names which aren't present in the
--`Lean.ConstMap`.
---/
--def compileDelta (delta : Lean.PersistentHashMap Lean.Name Lean.ConstantInfo)
--  : CompileM Unit := delta.forM fun n _ => discard $ compileConstName n
--
----def compileEnv (env: Lean.Environment)
----  : CompileM Unit := do
----  compileDelta env.getDelta
----  env.getConstMap.forM fun n _ => if !c.isUnsafe then discard $ compileConstName n else pure ()
--

instance : Nonempty (Task (CompileM.Result MetaAddress)) :=
  ⟨Task.pure (.ok default, default)⟩

structure ScheduleEnv where
  env: Lean.Environment
  blocks: CondensedBlocks
  comms: Map Lean.Name MetaAddress

structure ScheduleState where
  constTasks: Map Lean.Name (Task (Except IO.Error MetaAddress))
  blockTasks: Map Lean.Name (Task (Except IO.Error (Map Lean.Name MetaAddress)))

abbrev ScheduleM := ReaderT ScheduleEnv <| StateT ScheduleState IO

def ScheduleM.run (env: ScheduleEnv) (stt: ScheduleState) (c : ScheduleM α)
  : IO (α × ScheduleState)
  := StateT.run (ReaderT.run c env) stt

structure ScheduleStats where
  constWaiting: Nat
  constRunning: Nat
  constFinished: Nat
  blockWaiting: Nat
  blockRunning: Nat
  blockfinished: Nat
deriving Repr

partial def ScheduleState.stats : ScheduleState -> IO ScheduleStats
| ⟨constTasks, blockTasks⟩ => do
  let mut constWaiting := 0
  let mut constRunning := 0
  let mut constFinished := 0
  let mut blockWaiting := 0
  let mut blockRunning := 0
  let mut blockFinished := 0
  for (_, t) in constTasks do
    match <- IO.getTaskState t with
    | .waiting => constWaiting := constWaiting + 1
    | .running => constRunning := constRunning + 1
    | .finished => constFinished := constFinished + 1
  for (_, t) in blockTasks do
    match <- IO.getTaskState t with
    | .waiting => blockWaiting := blockWaiting + 1
    | .running => blockRunning := blockRunning + 1
    | .finished => blockFinished := blockFinished + 1
  return ⟨constWaiting, constRunning, constFinished, blockWaiting, blockRunning, blockFinished⟩

mutual

partial def ScheduleM.block (lo: Lean.Name)
  : ScheduleM (Task (Except IO.Error (Map Lean.Name MetaAddress))) := do
  if let some task := (<- get).blockTasks.get? lo then
    return task
  else
    let mut depTasks := []
    let all := (<- read).blocks.blocks.get! lo
    let comms := (<- read).comms
    let allRefs := (<- read).blocks.blockRefs.get! lo
    for ref in allRefs.filter (!all.contains ·) do
      let refTask <- ScheduleM.const ref
      depTasks := (ref, refTask)::depTasks
    let env := (<- read).env
    let task <- bindDeps {} env comms all lo depTasks
    modify fun stt => { stt with blockTasks := stt.blockTasks.insert lo task }
    return task
  where
    bindDeps
      (acc: Map Lean.Name MetaAddress)
      (env: Lean.Environment)
      (comms: Map Lean.Name MetaAddress)
      (all: Set Lean.Name)
      (n: Lean.Name)
      : List (Lean.Name × Task (Except IO.Error MetaAddress))
      -> IO (Task (Except IO.Error (Map Lean.Name MetaAddress)))
      | [] => IO.asTask <| do
        let (res, stt) <- CompileM.run
          (.init env acc comms all n) .init (compileConstant n)
        match res with
        | .ok _ => pure <| stt.constCache.filter (fun n _ => all.contains n)
        | .error e => do throw (IO.userError (<- e.pretty))
      | (ref, task) :: rest => IO.bindTask task (fun result =>
        match result with
        | .ok addr => bindDeps (acc.insert ref addr) env comms all n rest
        | .error e => do throw e
      )

partial def ScheduleM.const (n: Lean.Name)
  : ScheduleM (Task (Except IO.Error MetaAddress)) := do
  if let some task := (<- get).constTasks.get? n then
    return task
  else
    let lo := (<- read).blocks.lowLinks.get! n
    let blockTask <- match (<- get).blockTasks.get? lo with
      | some bt => pure bt
      | none => ScheduleM.block lo
    let task <- IO.bindTask blockTask (fun res => match res with
      | .ok map => match map.get? n with
        | .some x => IO.asTask <| pure x
        | .none => do
          throw (IO.userError (<- (CompileError.unknownConstant lo n).pretty))
      | .error e => throw e
    )
    modify fun stt => { stt with constTasks := stt.constTasks.insert n task }
    return task

end

partial def ScheduleM.env : ScheduleM Unit := do
  let env := (<- read).env
  let envSize := env.constants.fold (fun x _ _=> x + 1) 0
  let mut i := 1
  for (n,_) in (<- read).env.constants do
    --let stt <- get
    dbg_trace s!"scheduling {i}/{envSize} {n}"
    let _ <- ScheduleM.const n
    i := i + 1
  return ()


structure CompiledEnv where
  consts: Map Lean.Name MetaAddress
  refs :  Map Lean.Name (Set Lean.Name)
  blocks: CondensedBlocks

partial def CompileM.envTopological
  (env: Lean.Environment)
  (comms: Map Lean.Name MetaAddress)
  : IO CompiledEnv := do
  let refs: Map Lean.Name (Set Lean.Name) := GraphM.env env
  dbg_trace s!"constants: {refs.size}"
  let blocks := CondenseM.run env refs
  dbg_trace s!"lowlinks: {blocks.lowLinks.size}, blocks: {blocks.blocks.size}"

  let mut consts: Map Lean.Name MetaAddress := {}
  let mut remaining: Set Lean.Name := {}
  for (lo, _) in blocks.blocks do
    remaining := remaining.insert lo

  let numBlocks := remaining.size
  let mut i := 0

  dbg_trace s!"compiling {numBlocks} blocks"
  while !remaining.isEmpty do
    i := i + 1
    let pct := ((Float.ofNat remaining.size) / Float.ofNat numBlocks)
    dbg_trace s!"Wave {i}, {(1 - pct) * 100}%: {remaining.size}/{numBlocks} blocks remaining"

    let mut ready : Array (Lean.Name × Set Lean.Name) := #[]
    for r in remaining do
      let lo := blocks.lowLinks.get! r
      let all := blocks.blocks.get! lo
      let allDeps : Set Lean.Name := blocks.blockRefs.get! lo
      if allDeps.all (consts.contains ·) then
        ready := ready.push (r, all)
      else
        continue

    let mut tasks := #[]

    for (lo, all) in ready do
      --dbg_trace s!"Wave {i}: scheduling {lo}"
      let task <- IO.asTask <| CompileM.run
        (.init env consts comms all lo) .init (compileConstant lo)
      tasks := tasks.push task

    for task in tasks do
      match <- IO.wait task with
      | .ok (.ok _, stt) => consts := consts.union stt.constCache
      | .ok (.error e, _) => throw (IO.userError (<- e.pretty))
      | .error e => throw e

    for (r, _) in ready do
      remaining := remaining.erase r

  return ⟨consts, refs, blocks⟩

partial def CompileM.envScheduler
  (env: Lean.Environment)
  (comms: Map Lean.Name MetaAddress)
  : IO CompiledEnv := do
  let refs: Map Lean.Name (Set Lean.Name) := GraphM.env env
  println! s!"constants: {refs.size}"
  let blocks := CondenseM.run env refs
  println! s!"lowlinks: {blocks.lowLinks.size}, blocks: {blocks.blocks.size}"

  let (_, stt) <- ScheduleM.run ⟨env, blocks, comms⟩ ⟨{}, {}⟩ ScheduleM.env

  let mut consts := {}

  let tasksSize := stt.constTasks.size
  let mut i := 1

  while true do
    let stats <- ScheduleState.stats stt
    if stats.blockWaiting > 0 then
      println! s!"waiting {repr <| <- ScheduleState.stats stt}"
      continue
    else
      break

  for (n, task) in stt.constTasks do
    println! s!"waiting {i}/{tasksSize}"
    i := i + 1
    match (<- IO.wait task) with
    | .ok addr => consts := consts.insert n addr
    | .error e  => throw e

  return ⟨consts, refs, blocks⟩

--partial def CompileM.const
--  (name: Lean.Name) (env: Lean.Environment) (comms: Map Lean.Name MetaAddress)
--  : Except CompileError CompiledEnv := Id.run do
--  let refs: Map Lean.Name (Set Lean.Name) := GraphM.env env
--  let blocks := CondenseM.run env refs
--
--  let (_, stt) <- ScheduleM.run ⟨env, blocks, comms, refs⟩ ⟨{}⟩ (scheduleConst name)
--
--  let mut consts: Map Lean.Name MetaAddress := {}
--  let mut store: Map Address ByteArray := {}
--  let mut axioms: Set Lean.Name := {}
--
--  for (n, task) in stt.tasks do
--    dbg_trace "compiling {n}"
--    match task.get with
--    | .error e _ => return .error e
--    | .ok addr stt =>
--      consts := consts.insert n addr
--      store := store.union stt.store
--      axioms := axioms.union stt.axioms
--
--  return .ok ⟨consts, store, axioms, refs, blocks.count, blocks.alls⟩

--def CompileM.runIO' (c : CompileM α)
--  (stt: CompileState)
--  : IO (α × CompileState) := do
--  match <- c.run .init stt with
--  | (.ok a, stt) => return (a, stt)
--  | (.error e, _) => throw (IO.userError (<- e.pretty))
--
--def compileEnvIO (env: Lean.Environment) : IO (CompileState):= do
--  Prod.snd <$> (compileDelta env.getDelta).runIO env

--end Ix
