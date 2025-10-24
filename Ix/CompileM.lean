import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.Mutual
import Ix.Common
import Ix.CondenseM
import Ix.GroundM
--import Ix.Store
import Ix.SOrder
import Ix.Cronos

namespace Ix
open Ixon hiding Substring

structure CompileEnv where
  univCtx : List Lean.Name
  mutCtx  : MutCtx
  current : Lean.Name
deriving BEq, Ord

structure ExprCtx where
  univCtx : List Lean.Name
  mutCtx : List (Lean.Name × Nat)
deriving BEq, Hashable

def ExprCtx.fromEnv : CompileEnv -> ExprCtx
| ⟨u, m, _⟩ => ⟨u, m.toList⟩

def CompileEnv.init: CompileEnv := ⟨default, default, default⟩

structure CompileState where
  maxHeartBeats: USize
  env: Lean.Environment
  prng: StdGen
  store: Map Address ByteArray
  ixonCache: Map Ixon Address
  univCache: Map ((List Lean.Name) ×  Lean.Level) MetaAddress
  constCache: Map Lean.Name MetaAddress
  exprCache: Map (ExprCtx × Lean.Expr) MetaAddress
  synCache: Map Lean.Syntax Ixon.Syntax
  nameCache: Map Lean.Name Address
  strCache: Map String Address
  comms: Map Lean.Name MetaAddress
  constCmp: Map (Lean.Name × Lean.Name) Ordering
  cstagePatch : Map Lean.Name Lean.Name
  --exprCmp: Map (CompileEnv × Lean.Expr × Lean.Expr) Ordering
  alls: Map Lean.Name (Set Lean.Name)
  axioms: Map Lean.Name MetaAddress
  blocks: Map MetaAddress Unit
  cronos: Cronos

def CompileState.init (env: Lean.Environment)
  (alls: Map Lean.Name (Set Lean.Name))
  (seed: Nat) (maxHeartBeats: USize := 200000)
  : CompileState :=
  ⟨maxHeartBeats, env, mkStdGen seed, default, default, default, default,
  default, default, default, default, default, default, default,
  alls, default, default, default⟩

inductive CompileError where
| unknownConstant : Lean.Name -> CompileError
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
| .unknownConstant n => pure s!"Unknown constant '{n}'"
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

def CompileM.run (env: CompileEnv) (stt: CompileState) (c : CompileM α)
  : IO (Except CompileError α × CompileState)
  := StateT.run (ExceptT.run (ReaderT.run c env)) stt

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

--def storeConst (const: Ixon): CompileM Address := do
--  liftM (Store.writeConst const).toIO

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
  --dbg_trace "storeIxon ser {(<- get).store.size} {(<- read).current}"
  match (<- get).ixonCache.find? ixon with
  | some addr => pure addr
  | none => do
    let bytes := Ixon.ser ixon
    let addr := Address.blake3 bytes
    --dbg_trace "storeIxon hash {addr} {(<- read).current}"
    modifyGet fun stt => (addr, { stt with
      store := stt.store.insert addr bytes
    })

def getIxon (addr: Address) : CompileM Ixon := do
  match (<- get).store.find? addr with
  | some bytes => match Ixon.de bytes with
    | .ok ixon => pure ixon
    | .error e => throw <| .badIxonDeserialization addr e
  | none => throw <| .unknownStoreAddress addr

def getAll (name: Lean.Name) : CompileM (Set Lean.Name) := do
  match (<- get).alls.get? name with
  | some set => pure set
  | none => throw <| .condensationError name

def storeString (str: String): CompileM Address := do
  match (<- get).strCache.find? str with
  | some addr => pure addr
  | none => do
    let bytes := str.toUTF8
    let addr := Address.blake3 bytes
    modifyGet fun stt => (addr, { stt with
      strCache := stt.strCache.insert str addr
      store := stt.store.insert addr bytes
    })

def storeNat (nat: Nat): CompileM Address := do
  let bytes := nat.toBytesLE
  let addr := Address.blake3 ⟨bytes⟩
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr ⟨bytes⟩
  })

def storeSerial [Serialize A] (a: A): CompileM Address := do
  let bytes := Ixon.ser a
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def storeMeta (meta: Metadata): CompileM Address := do
  let bytes := Ixon.ser meta
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def compileName (name: Lean.Name): CompileM Address := do
  match (<- get).nameCache.find? name with
  | some addr =>
  --dbg_trace "compileName cached {(<- read).current} {addr} {name}"
    pure addr
  | none => do
    let addr <- go name
  --dbg_trace "compileName {(<- read).current} {addr} {name}"
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
  let ctx := (<- read).univCtx
  match (<- get).univCache.find? (ctx, lvl) with
  | some l => pure l
  | none => do
    --dbg_trace "compileLevel go {(<- get).univAddrs.size} {(<- read).current}"
    let (anon, meta) <- go lvl
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    modifyGet fun stt => (maddr, { stt with
      univCache := stt.univCache.insert (ctx, lvl) maddr
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

def compileKVMaps (maps: List Lean.KVMap): CompileM Address := do
  storeIxon (.meta ⟨<- maps.mapM go⟩)
  where
    go (map: Lean.KVMap): CompileM Metadatum := do
    let mut list := #[]
    for (name, dataValue) in map do
      let n <- compileName name
      let d <- compileDataValue dataValue
      list := list.push (n, d)
    pure <| .kvmap list.toList

def findLeanConst (name : Lean.Name) : CompileM Lean.ConstantInfo := do
  match (<- get).env.constants.find? name with
  | some const => pure const
  | none => throw $ .unknownConstant name
    --let name2 := name.append (Lean.Name.mkSimple "_cstage2")
    --match (<- get).env.constants.find? name2 with
    -- | some const => do
    --  let _ <- compileName name2
    --  modifyGet fun stt => (const, { stt with
    --    cstagePatch := stt.cstagePatch.insert name name2
    --  })
    -- | none => 

def MutConst.mkIndc (i: Lean.InductiveVal) : CompileM MutConst := do
  let ctors <- i.ctors.mapM getCtor
  return .indc ⟨i.name, i.levelParams, i.type, i.numParams, i.numIndices, i.all,
    ctors, i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩
  where
    getCtor (name: Lean.Name) : CompileM (Lean.ConstructorVal) := do
      match (<- findLeanConst name) with
      | .ctorInfo c => pure c
      | _ => throw <| .invalidConstantKind name "constructor" ""

--def mkProjCtx (mss: List (List MutConst)) : Map Lean.Name Nat := Id.run do
--  let mut ctx := {}
--  let mut i := 0
--  for ms in mss do
--    for m in ms do
--      ctx := ctx.insert m.name i
--    i := i + 1
--  return ctx

mutual

partial def compileExpr: Lean.Expr -> CompileM MetaAddress 
| expr => outer [] expr
  where
    outer (kvs: List Lean.KVMap) (expr: Lean.Expr): CompileM MetaAddress := do
      let ctx := ExprCtx.fromEnv (<- read)
      match (<- get).exprCache.find? (ctx, expr) with
      | some x => pure x
      | none => do
        let (anon, meta) <- go kvs expr
        let anonAddr <- storeIxon anon
        let metaAddr <- storeIxon meta
        let maddr := ⟨anonAddr, metaAddr⟩
        modifyGet fun stt => (maddr, { stt with
          exprCache := stt.exprCache.insert (ctx, expr) maddr
        })
    go (kvs: List Lean.KVMap): Lean.Expr -> CompileM (Ixon × Ixon)
    | (.mdata kv x) => go (kv::kvs) x
    | .bvar idx => do
      let md <- compileKVMaps kvs
      let data := .evar idx
      let meta := .meta ⟨[.link md]⟩
      pure (data, meta)
    | .sort univ => do
      let md <- compileKVMaps kvs
      let ⟨udata, umeta⟩ <- compileLevel univ
      let data := .esort udata
      let meta := .meta ⟨[.link md, .link umeta]⟩
      pure (data, meta)
    | .const name lvls => do
      let md <- compileKVMaps kvs
      let n <- compileName name
      let us <- lvls.mapM compileLevel
      match (← read).mutCtx.find? name with
      | some idx => 
      --dbg_trace s!"compileExpr {(<- read).current}, const rec {name} {idx}, mutCtx: {repr (<- read).mutCtx}, md {md}, us: {repr us}, n: {n}"
        let data := .erec idx (us.map (·.data))
        let meta := .meta ⟨[.link md, .link n, .links (us.map (·.meta))]⟩
        pure (data, meta)
      | none => do
        let ref <- match (<- get).comms.find? name with
          | some comm => pure comm
          | none => compileConstName name
      --dbg_trace s!"compileExpr {(<- read).current}, const ref {name}, mutCtx: {repr (<- read).mutCtx}, md {md}, repr {us}, ref {ref}"
        let data := .eref ref.data (us.map (·.data))
        let meta := .meta ⟨[.link md, .link n, .link ref.meta, .links (us.map (·.meta))]⟩
        pure (data, meta)
    | .app func argm => do
      let md <- compileKVMaps kvs
      let f <- compileExpr func
      let a <- compileExpr argm
      let data := .eapp f.data a.data
      let meta := .meta ⟨[.link md, .link f.meta, .link a.meta]⟩
      pure (data, meta)
    | .lam name type body info => do
      let md <- compileKVMaps kvs
      let n <- compileName name
      let t <- compileExpr type
      let b <- compileExpr body
      let data := .elam t.data b.data
      let meta := .meta ⟨[.link md, .link n, .info info, .link t.meta, .link b.meta]⟩
      pure (data, meta)
    | .forallE name type body info => do
      let md <- compileKVMaps kvs
      let n <- compileName name
      let t <- compileExpr type
      let b <- compileExpr body
      let data := .eall t.data b.data
      let meta := .meta ⟨[.link md, .link n, .info info, .link t.meta, .link b.meta]⟩
      pure (data, meta)
    | .letE name type value body nD => do
      let md <- compileKVMaps kvs
      let n <- compileName name
      let t <- compileExpr type
      let v <- compileExpr value
      let b <- compileExpr body
      let data := .elet nD t.data v.data b.data
      let meta := .meta ⟨[.link md, .link n, .link t.meta, .link v.meta, .link b.meta]⟩
      pure (data, meta)
    | .lit (.natVal n) => do
      let md <- compileKVMaps kvs
      pure (.enat (<- storeNat n), .meta ⟨[.link md]⟩)
    | .lit (.strVal s) => do
      let md <- compileKVMaps kvs
      pure (.estr (<- storeString s), .meta ⟨[.link md]⟩)
    | .proj typeName idx struct => do
      let md <- compileKVMaps kvs
      let t <- match (<- get).comms.find? typeName with
        | some comm => pure comm
        | none => compileConstName typeName
      let n <- compileName typeName
      let s <- compileExpr struct
      let data := .eprj t.data idx s.data
      let meta := .meta ⟨[.link md, .link n, .link t.meta, .link s.meta]⟩
      pure (data, meta)
    | expr@(.fvar ..)  => throw $ .exprFreeVariable expr
    | expr@(.mvar ..)  => throw $ .exprMetavariable expr

partial def compileConstName (name: Lean.Name): CompileM MetaAddress := do
  match (<- get).constCache.find? name with
  | some x => pure x
  | none => do
    let (anon, meta) <- do
      if name == Lean.Name.mkSimple "_obj" then pure (.prim .obj, .meta ⟨[]⟩)
      else if name == Lean.Name.mkSimple "_neutral" then pure (.prim .neutral, .meta ⟨[]⟩)
      else if name == Lean.Name.mkSimple "_unreachable" then pure (.prim .unreachable, .meta ⟨[]⟩)
      else do findLeanConst name >>= compileConstant
    --let stt <- get
    --dbg_trace "✓ compileConst {const.name}"
    --dbg_trace "store {stt.store.size}"
    --dbg_trace "constCache {stt.constCache.size}"
    --dbg_trace "exprCache {stt.exprCache.size}"
    --dbg_trace "nameCache {stt.nameCache.size}"
    --dbg_trace "synCache {stt.synCache.size}"
    --dbg_trace "strCache {stt.strCache.size}"
    --dbg_trace "univCache {stt.univCache.size}"
    let maddr := ⟨<- storeIxon anon, <- storeIxon meta⟩
    modifyGet fun stt => (maddr, { stt with
      constCache := stt.constCache.insert name maddr
    })
partial def compileConstant : Lean.ConstantInfo -> CompileM (Ixon × Ixon)
| c => do
--dbg_trace "compileConstant {c.name}"
  .resetCtx c.name <| compileConstant' c

partial def compileConstant' : Lean.ConstantInfo -> CompileM (Ixon × Ixon)
| .defnInfo val => compileMutual (MutConst.mkDefn val)
| .thmInfo val => compileMutual (MutConst.mkTheo val)
| .opaqueInfo val => compileMutual (MutConst.mkOpaq val)
| .inductInfo val => MutConst.mkIndc val >>= compileMutual
| .ctorInfo val => do match <- findLeanConst val.induct with
  | .inductInfo ind => do
    let _ <- MutConst.mkIndc ind >>= compileMutual
    match (<- get).constCache.find? val.name with
    | some ⟨data, meta⟩ => do pure (<- getIxon data, <- getIxon meta)
    | none => throw <| .mutualBlockMissingProjection val.name
  | c => throw <| .invalidConstantKind c.name "inductive" c.ctorName
| .recInfo val => do
--dbg_trace "compileConstant recInfo {val.name} mutCtx {repr <| (<- read).mutCtx}"
  compileMutual (MutConst.recr val)
| .axiomInfo ⟨⟨name, lvls, type⟩, isUnsafe⟩ => .withLevels lvls do
  let n <- compileName name
  let ls <- lvls.mapM compileName
  let t <- compileExpr type
  let data := .axio ⟨isUnsafe, lvls.length, t.data⟩
  let meta := .meta ⟨[.link n, .links ls, .link t.meta]⟩
  pure (data, meta)
| .quotInfo ⟨⟨name, lvls, type⟩, kind⟩ => .withLevels lvls do
  let n <- compileName name
  let ls <- lvls.mapM compileName
  let t <- compileExpr type
  let data := .quot ⟨kind, lvls.length, t.data⟩
  let meta := .meta ⟨[.link n, .links ls, .link t.meta]⟩
  pure (data, meta)

partial def compileDefn: Ix.Def -> CompileM (Ixon.Definition × Ixon.Metadata)
| d => .withLevels d.levelParams do
  let n <- compileName d.name
  let ls <- d.levelParams.mapM compileName
  let t <- compileExpr d.type
  let v <- compileExpr d.value
  let as <- d.all.mapM compileName
  let data := ⟨d.kind, d.safety, ls.length, t.data, v.data⟩
  let meta := ⟨[.link n, .links ls, .hints d.hints, .link t.meta, .link v.meta, .links as]⟩
  return (data, meta)

partial def compileRule: Lean.RecursorRule -> CompileM (Ixon.RecursorRule × (Address × Address))
| r => do
  let n <- compileName r.ctor
  let rhs <- compileExpr r.rhs
  pure (⟨r.nfields, rhs.data⟩, (n, rhs.meta))

partial def compileRecr: Lean.RecursorVal -> CompileM (Ixon.Recursor × Metadata)
| r => .withLevels r.levelParams <| do
--dbg_trace s!"compileRecr {(<- read).current} {repr <| r.name} mutCtx: {repr (<- read).mutCtx}"
  let n <- compileName r.name
  let ls <- r.levelParams.mapM compileName
  let t <- compileExpr r.type
  let rules <- r.rules.mapM compileRule
  let as <- r.all.mapM compileName
  let data := ⟨r.k, r.isUnsafe, ls.length, r.numParams, r.numIndices,
    r.numMotives, r.numMinors, t.data, rules.map (·.1)⟩
  let meta := ⟨[.link n, .links ls, .link t.meta, .map (rules.map (·.2)), .links as]⟩
  pure (data, meta)

partial def compileConstructor (induct: Address)
: Lean.ConstructorVal -> CompileM (Ixon.Constructor × Metadata)
| c => .withLevels c.levelParams <| do
  let n <- compileName c.name
  let ls <- c.levelParams.mapM compileName
  let t <- compileExpr c.type
  let data := ⟨c.isUnsafe, ls.length, c.cidx, c.numParams, c.numFields, t.data⟩
  let meta := ⟨[.link n, .links ls, .link t.meta, .link induct]⟩
  pure (data, meta)

partial def compileIndc: Ix.Ind -> CompileM (Ixon.Inductive × Map Address Address)
| ⟨name, lvls, type, ps, is, all, ctors, nest, rcr, refl, usafe⟩ =>
  .withLevels lvls do 
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
  let meta := ⟨[.link n, .links ls, .link t.meta, .links cms.toList, .links as]⟩
  let m <- storeMeta meta
  metaMap := metaMap.insert n m
  pure (data, metaMap)

partial def compileMutual : MutConst -> CompileM (Ixon × Ixon)
| const => do
--dbg_trace s!"compileMutual {const.name}"
  let all: Set Lean.Name <- getAll const.name
--dbg_trace s!"compileMutual {const.name} all: {repr all}"
  if all == {const.name} &&
    (const matches .defn _ || const matches .recr _) then do
    match const with
    | .defn d => do
      let (data, meta) <- .withMutCtx (.single d.name 0) <| compileDefn d
      pure (.defn data, .meta meta)
    | .recr r => do
      let (data, meta) <- .withMutCtx (.single r.name 0) <| compileRecr r
      pure (.recr data, .meta meta)
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
    let block := ⟨<- storeIxon data, <- storeMeta ⟨[.muts mutMeta, .map ctx, .map metas.toList]⟩⟩
    modify fun stt => { stt with blocks := stt.blocks.insert block () }
    -- then add all projections, returning the inductive we started with
    let mut ret? : Option (Ixon × Ixon) := none
    --let mut projCtx := mkProjCtx mutConsts
    for const' in consts do
      let idx <- do match mutCtx.find? const'.name with
      | some idx => pure idx
      | none => throw $ .cantFindMutIndex const'.name mutCtx
      let n <- compileName const'.name
      let meta <- do match metas.find? n with
      | some meta => pure ⟨[.link block.meta, .link meta]⟩
      | none => throw $ .cantFindMutMeta const'.name metas
      let data := match const with
      | .defn _ => .dprj ⟨idx, block.data⟩
      | .indc _ => .iprj ⟨idx, block.data⟩
      | .recr _ => .rprj ⟨idx, block.data⟩
      let addr := ⟨<- storeIxon data, <- storeMeta meta⟩
      modify fun stt => { stt with
        constCache := stt.constCache.insert const'.name addr
      }
      if const'.name == const.name then ret? := some (data, .meta meta)
      for ctor in const'.ctors do
        let cdata := .cprj ⟨idx, ctor.cidx, block.data⟩
        let cn <- compileName ctor.name
        let cmeta <- do match metas.find? cn with
        | some meta => pure ⟨[.link block.meta, .link meta]⟩
        | none => throw $ .cantFindMutMeta const'.name metas
        let caddr := ⟨<- storeIxon cdata, <- storeMeta cmeta⟩
        modify fun stt => { stt with
          constCache := stt.constCache.insert ctor.name caddr
        }
    match ret? with
    | some ret => return ret
    | none => throw $ .mutualBlockMissingProjection const.name

/-- Compile a mutual block --/
partial def compileMutConsts: List (List MutConst)
  -> CompileM (Ixon × Map Address Address)
| classes => do
--dbg_trace s!"compileMutConsts {(<- read).current} {repr <| classes.map (·.map (·.name))} mutCtx: {repr (<- read).mutCtx}"
  let mut data := #[]
  let mut meta := {}
  -- iterate through each equivalence class
  for constClass in classes do
    let mut classData := #[]
    -- compile each constant in a class
    for const in constClass do
      match const with
      | .indc x => do
        let (i, m) <- compileIndc x
        classData := classData.push (.indc i)
        meta := meta.union m
      | .defn x => do
        let (d, m) <- compileDefn x
        classData := classData.push (.defn d)
        meta := meta.insert (<- compileName x.name) (<- storeMeta m)
      | .recr x => do
        let (r, m) <- compileRecr x
        classData := classData.push (.recr r)
        meta := meta.insert (<- compileName x.name) (<- storeMeta m)
    -- make sure we have no empty classes and all defs in a class are equal
    match classData.toList with
      | [] => throw (.badMutualBlock classes)
      | [x] => data := data.push x
      | x::xs =>
        if xs.foldr (fun y acc => (y == x) && acc) true
        then data := data.push x
        else throw (.badMutualBlock classes)
  pure (.muts data.toList, meta)

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

/-- AST comparison of two Lean definitions. --/
partial def compareConst (ctx: MutCtx) (x y: MutConst)
  : CompileM Ordering := do
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

partial def eqConst (ctx: MutCtx) (x y: MutConst) : CompileM Bool :=
  (fun o => o == .eq) <$> compareConst ctx x y

/-- A name-irrelevant ordering of Lean expressions --/
partial def compareExpr (ctx: MutCtx) (xlvls ylvls: List Lean.Name)
  : Lean.Expr → Lean.Expr → CompileM SOrder
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
    match ctx.find? x, ctx.find? y with
    | some nx, some ny => return ⟨false, compare nx ny⟩
    | none, some _ => return ⟨true, .gt⟩
    | some _, none => return ⟨true, .lt⟩
    | none, none =>
      if x == y then return ⟨true, .eq⟩
      else do
      --dbg_trace s!"compareExpr const {(<- read).current} consts {x} {y}"
        let x' <- compileConstName x
        let y' <- compileConstName y
        return ⟨true, compare x' y'⟩
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
  | .proj tnx ix tx, .proj tny iy ty => 
    SOrder.cmpM (pure ⟨true, compare ix iy⟩) <|
    SOrder.cmpM (compareExpr ctx xlvls ylvls tx ty) <|
    match ctx.find? tnx, ctx.find? tny with
    | some nx, some ny => return ⟨false, compare nx ny⟩
    | none, some _ => return ⟨true, .gt⟩
    | some _, none => return ⟨true, .lt⟩
    | none, none =>
      if tnx == tny then return ⟨true, .eq⟩
      else do
      --dbg_trace s!"compareExpr proj {(<- read).current} consts {tnx} {tny}"
        let x' <- compileConstName tnx
        let y' <- compileConstName tny
        return ⟨true, compare x' y'⟩
end

partial def makeLeanDef
  (name: Lean.Name) (levelParams: List Lean.Name) (type value: Lean.Expr) 
  : Lean.DefinitionVal :=
  { name, levelParams, type, value, hints := .opaque, safety := .safe }

partial def tryAddLeanDef (defn: Lean.DefinitionVal) : CompileM Unit := do
  match (<- get).env.constants.find? defn.name with
  | some _ => pure ()
  | none => do
    let env <- (·.env) <$> get
    let maxHeartBeats <- (·.maxHeartBeats) <$> get
    let decl := Lean.Declaration.defnDecl defn
    match Lean.Environment.addDeclCore env maxHeartBeats decl .none with
    | .ok e => do
      modify fun stt => { stt with env := e }
      return ()
    | .error e => throw $ .kernelException e

partial def addDef (lvls: List Lean.Name) (typ val: Lean.Expr) : CompileM MetaAddress := do
  --let typ' <- compileExpr typ
  --let val' <- compileExpr val
  let anon := .defnInfo ⟨⟨.anonymous, lvls, typ⟩, val, .opaque, .safe, []⟩
  let (data, meta) <- compileConstant anon
  let anonAddr := ⟨<- storeIxon data, <- storeIxon meta⟩
  let name := anonAddr.data.toUniqueName
  let const := .defnInfo ⟨⟨name, lvls, typ⟩, val, .opaque, .safe, []⟩
  let (data, meta) <- compileConstant const
  let addr := ⟨<- storeIxon data, <- storeIxon meta⟩
  if addr.data != anonAddr.data then
    throw <| .alphaInvarianceFailure anon anonAddr const addr
  else
    tryAddLeanDef (makeLeanDef name lvls typ val)
    return addr

partial def commitConst (addr: MetaAddress) (secret: Address) : CompileM MetaAddress := do
  let comm := Ixon.comm ⟨secret, addr.data⟩
  let commAddr <- storeIxon comm
  let commMeta := Ixon.comm ⟨secret, addr.meta⟩
  let commMetaAddr <- storeIxon commMeta
  let addr' := ⟨commAddr, commMetaAddr⟩
  modify fun stt => { stt with
    comms := stt.comms.insert commAddr.toUniqueName addr'
  }
  return addr'

partial def commitDef (lvls: List Lean.Name) (typ val: Lean.Expr) (secret: Address): CompileM MetaAddress := do
  let addr <- addDef lvls typ val
  let addr' <- commitConst addr secret
  tryAddLeanDef (makeLeanDef addr'.data.toUniqueName lvls typ val)
  --tryAddLeanDecl (makeLeanDef ca.toUniqueName lvls typ (mkConst a.toUniqueName []))
  return addr'

partial def storeLevel (lvls: Nat) (secret: Option Address): CompileM Address := do
  let addr <- storeNat lvls
  match secret with
  | some secret => do
    let comm := .comm ⟨secret, addr⟩
    let commAddr <- storeIxon comm
    modify fun stt => { stt with
      comms := stt.comms.insert commAddr.toUniqueName ⟨commAddr, commAddr⟩
    }
    return commAddr
  | none => return addr
--
----partial def checkClaim
----  (const: Lean.Name)
----  (type: Lean.Expr)
----  (sort: Lean.Expr)
----  (lvls: List Lean.Name)
----  (secret: Option Address)
----  : CompileM (Claim × Address × Address) := do
----  let leanConst <- findLeanConst const
----  let valAddr <- compileConst leanConst >>= comm
----  let typeAddr <- addDef lvls sort type >>= comm
----  let lvls <- packLevel lvls.length commit
----  return (Claim.checks (CheckClaim.mk lvls type value), typeMeta, valMeta)
----  where
----    commit (c: Ix.Const) : MetaAddress := do
----      match commit with
----      | none => dematerializeConst c
----      | some secret => 
----
----    if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a
--
----
----partial def evalClaim
----  (lvls: List Lean.Name)
----  (input: Lean.Expr)
----  (output: Lean.Expr)
----  (type: Lean.Expr)
----  (sort: Lean.Expr)
----  (commit: Bool)
----  : CompileM (Claim × Address × Address × Address) := do
----  let (input, inputMeta) <- addDef lvls type input >>= comm
----  let (output, outputMeta) <- addDef lvls type output >>= comm
----  let (type, typeMeta) <- addDef lvls sort type >>= comm
----  let lvlsAddr <- packLevel lvls.length commit
----  return (Claim.evals (EvalClaim.mk lvlsAddr input output type), inputMeta, outputMeta, typeMeta)
----  where
----    comm a := if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a


/--
Content-addresses the "delta" of an environment, that is, the content that is
added on top of the imports.

Important: constants with open references in their expressions are filtered out.
Open references are variables that point to names which aren't present in the
`Lean.ConstMap`.
-/
def compileDelta (delta : Lean.PersistentHashMap Lean.Name Lean.ConstantInfo)
  : CompileM Unit := delta.forM fun n _ => discard $ compileConstName n

--def compileEnv (env: Lean.Environment)
--  : CompileM Unit := do
--  compileDelta env.getDelta
--  env.getConstMap.forM fun n _ => if !c.isUnsafe then discard $ compileConstName n else pure ()

def CompileM.runIO (c : CompileM α) 
  (env: Lean.Environment)
  (maxHeartBeats: USize := 200000)
  (seed : Option Nat := .none)
  : IO (α × CompileState) := do
  let gstt <- GroundM.env env
  let alls := CondenseM.run env gstt.outRefs
  let seed <- match seed with
    | .none => IO.monoNanosNow
    | .some s => pure s
  match <- c.run .init (.init env alls seed maxHeartBeats) with
  | (.ok a, stt) => return (a, stt)
  | (.error e, _) => throw (IO.userError (<- e.pretty))

def CompileM.runIO' (c : CompileM α) 
  (stt: CompileState)
  : IO (α × CompileState) := do
  match <- c.run .init stt with
  | (.ok a, stt) => return (a, stt)
  | (.error e, _) => throw (IO.userError (<- e.pretty))

def compileEnvIO (env: Lean.Environment) : IO (CompileState):= do
  Prod.snd <$> (compileDelta env.getDelta).runIO env

end Ix
