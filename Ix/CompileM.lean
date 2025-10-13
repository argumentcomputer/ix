import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.IR
import Ix.Common
import Ix.CondenseM
--import Ix.Store
import Ix.SOrder
import Ix.Cronos


namespace Ix
open Ixon hiding Substring

structure CompileEnv where
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  mutCtx  : MutCtx
  current : Lean.Name
deriving BEq, Ord

def CompileEnv.init: CompileEnv := ⟨default, default, default, default⟩

structure CompileState where
  maxHeartBeats: USize
  env: Lean.Environment
  prng: StdGen
  store: Map Address ByteArray
  ixonCache: Map Ixon Address
  univCache: Map Lean.Level MetaAddress
  constCache: Map Lean.Name MetaAddress
  exprCache: Map Lean.Expr MetaAddress
  synCache: Map Lean.Syntax Ixon.Syntax
  nameCache: Map Lean.Name Address
  strCache: Map String Address
  comms: Map Lean.Name MetaAddress
  constCmp: Map (Lean.Name × Lean.Name) Ordering
  --exprCmp: Map (CompileEnv × Lean.Expr × Lean.Expr) Ordering
  alls: Map Lean.Name (Set Lean.Name)
  axioms: Map Lean.Name MetaAddress
  blocks: Map MetaAddress Unit
  cronos: Cronos

def collectRecursors (env: Lean.Environment) : Map Lean.Name (Set Lean.Name) := Id.run do
 let mut map := {}
 for (n, c) in env.constants do
  match c with
  | .recInfo val => do
    map := map.alter val.getMajorInduct <| fun x => match x with
      | .none => .some {n}
      | .some s => .some (s.insert n)
  | _ => continue
 return map

def CompileState.init (env: Lean.Environment) (seed: Nat) (maxHeartBeats: USize := 200000)
  : CompileState :=
  ⟨maxHeartBeats, env, mkStdGen seed, default, default, default, default,
  default, default, default, default, default, default, CondenseM.run env,
  default, default, default⟩

inductive CompileError where
| unknownConstant : Lean.Name -> CompileError
| levelMetavariable : Lean.Level -> CompileError
| exprMetavariable : Lean.Expr -> CompileError
| exprFreeVariable : Lean.Expr -> CompileError
| invalidBVarIndex : Nat -> CompileError
| levelNotFound : Lean.Name -> List Lean.Name -> String -> CompileError
| invalidConstantKind : Lean.Name -> String -> String -> CompileError
| compileMutualBlockMissingProjection : Lean.Name -> CompileError
| compileInductiveBlockMissingProjection : Lean.Name -> CompileError
--| nonRecursorExtractedFromChildren : Lean.Name → CompileError
| cantFindMutDefIndex : Lean.Name -> CompileError
| kernelException : Lean.Kernel.Exception → CompileError
--| cantPackLevel : Nat → CompileError
--| nonCongruentInductives : PreInd -> PreInd -> CompileError
| alphaInvarianceFailure : Lean.ConstantInfo -> MetaAddress -> Lean.ConstantInfo -> MetaAddress -> CompileError
--| dematBadMutualBlock: MutualBlock -> CompileError
--| dematBadInductiveBlock: InductiveBlock -> CompileError
| badMutualBlock: List (List PreDef) -> CompileError
| badInductiveBlock: List (List PreInd) -> CompileError
| badRecursorBlock: List (List Lean.RecursorVal) -> CompileError
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
| .levelNotFound n ns msg => pure s!"'Level {n}' not found in '{ns}', {msg}"
| .invalidConstantKind n ex gt => pure s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
| .compileMutualBlockMissingProjection n => pure s!"Constant '{n}' wasn't content-addressed in mutual block"
| .compileInductiveBlockMissingProjection n => pure s!"Constant '{n}' wasn't content-addressed in inductive block"
| .cantFindMutDefIndex n => pure s!"Can't find index for mutual definition '{n}'"
| .kernelException e => (·.pretty 80) <$> (e.toMessageData .empty).format
| .alphaInvarianceFailure x xa y ya => 
  pure s!"alpha invariance failure {repr x} hashes to {xa}, but {repr y} hashes to {ya}"
| .badMutualBlock block => pure s!"bad mutual block {repr block}"
| .badInductiveBlock block => pure s!"bad mutual block {repr block}"
| .badRecursorBlock block => pure s!"bad mutual block {repr block}"
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
def withCurrent (name: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with current := name }

-- add binding name to local context
def withBinder (name: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def withLevels (lvls : List Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def withMutCtx (mutCtx : MutCtx) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

-- reset local context
def resetCtx (current: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := [], bindCtx := [], mutCtx := {}, current }

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
  | some addr => pure addr
  | none => do
    let addr <- go name
    modifyGet fun stt => (addr, { stt with
      nameCache := stt.nameCache.insert name addr
    })
  where
    go : Lean.Name -> CompileM Address
    | .anonymous => pure <| Address.blake3 ⟨#[]⟩
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
      throw $ .levelNotFound x xctx s!"compareLevel"
    | _,       none    => 
      throw $ .levelNotFound y yctx s!"compareLevel"

/-- Canonicalizes a Lean universe level --/
def compileLevel (lvl: Lean.Level): CompileM MetaAddress := do
  match (<- get).univCache.find? lvl with
  | some l => pure l
  | none => do
    --dbg_trace "compileLevel go {(<- get).univAddrs.size} {(<- read).current}"
    let (anon, meta) <- go lvl
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
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
      | none   => throw $ .levelNotFound n lvls s!"compileLevel"
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
| .ofNat i => .ofName <$> storeNat i
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
  match (← get).env.constants.find? name with
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

partial def compileExpr: Lean.Expr -> CompileM MetaAddress 
| expr => outer [] expr
  where
    outer (kvs: List Lean.KVMap) (expr: Lean.Expr): CompileM MetaAddress := do
      match (<- get).exprCache.find? expr with
      | some x => pure x
      | none => do
        let (anon, meta) <- go kvs expr
        let anonAddr <- storeIxon anon
        let metaAddr <- storeIxon meta
        let maddr := ⟨anonAddr, metaAddr⟩
        modifyGet fun stt => (maddr, { stt with
          exprCache := stt.exprCache.insert expr maddr
        })
    go (kvs: List Lean.KVMap): Lean.Expr -> CompileM (Ixon × Ixon)
    | (.mdata kv x) => go (kv::kvs) x
    | .bvar idx => do
      let md <- compileKVMaps kvs
      let data := .evar idx
      let sort := .meta ⟨[.link md]⟩
      pure (data, sort)
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
        let data := .erec idx (us.map (·.data))
        let meta := .meta ⟨[.link md, .link n, .links (us.map (·.meta))]⟩
        pure (data, meta)
      | none => do
        let ref <- match (<- get).comms.find? name with
          | some comm => pure comm
          | none => findLeanConst name >>= compileConst
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
        | none => findLeanConst typeName >>= compileConst
      let n <- compileName typeName
      let s <- compileExpr struct
      let data := .eprj t.data idx s.data
      let meta := .meta ⟨[.link md, .link n, .link t.meta, .link s.meta]⟩
      pure (data, meta)
    | expr@(.fvar ..)  => throw $ .exprFreeVariable expr
    | expr@(.mvar ..)  => throw $ .exprMetavariable expr

partial def compileConst (const: Lean.ConstantInfo): CompileM MetaAddress := do
  match (<- get).constCache.find? const.name with
  | some x => pure x
  | none => resetCtx const.name <| do
    let (anon, meta) <- go const
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
      constCache := stt.constCache.insert const.name maddr
    })
  where
    go : Lean.ConstantInfo -> CompileM (Ixon × Ixon)
    | .defnInfo val => compileDefs (mkPreDef val)
    | .thmInfo val => compileDefs (mkPreTheorem val)
    | .opaqueInfo val => compileDefs (mkPreOpaque val)
    | .inductInfo val => mkPreInd val >>= compileInds
    | .ctorInfo val => do match <- findLeanConst val.induct with
      | .inductInfo ind => do
        let _ <- mkPreInd ind >>= compileInds
        match (<- get).constCache.find? const.name with
        | some ⟨data, meta⟩ => do pure (<- getIxon data, <- getIxon meta)
        | none => throw <| .compileInductiveBlockMissingProjection const.name
      | c => throw <| .invalidConstantKind c.name "inductive" c.ctorName
    -- compile recursors through their parent inductive
    | .recInfo val => compileRecs val
    | .axiomInfo ⟨⟨name, lvls, type⟩, isUnsafe⟩ => withLevels lvls do
      let n <- compileName name
      let ls <- lvls.mapM compileName
      let t <- compileExpr type
      let data := .axio ⟨isUnsafe, lvls.length, t.data⟩
      let meta := .meta ⟨[.link n, .links ls, .link t.meta]⟩
      pure (data, meta)
    | .quotInfo ⟨⟨name, lvls, type⟩, kind⟩ => withLevels lvls do
      let n <- compileName name
      let ls <- lvls.mapM compileName
      let t <- compileExpr type
      let data := .quot ⟨kind, lvls.length, t.data⟩
      let meta := .meta ⟨[.link n, .links ls, .link t.meta]⟩
      pure (data, meta)

partial def compileDef: PreDef -> CompileM (Ixon.Definition × Ixon.Metadata)
| d => withLevels d.levelParams do
  let n <- compileName d.name
  let ls <- d.levelParams.mapM compileName
  let t <- compileExpr d.type
  let v <- compileExpr d.value
  let as <- d.all.mapM compileName
  let data := ⟨d.kind, d.safety, ls.length, t.data, v.data⟩
  let meta := ⟨[.link n, .links ls, .hints d.hints, .link t.meta, .link v.meta, .links as]⟩
  return (data, meta)

partial def compileMutDefs: List (List PreDef) -> CompileM (Ixon × Ixon)
| defs => do
  let mut data := #[]
  let mut meta := #[]
  -- iterate through each equivalence class
  for defsClass in defs do
    let mut classData := #[]
    let mut classMeta := #[]
    -- compile each def in a class
    for defn in defsClass do
      let (defn', meta') <- compileDef defn
      classData := classData.push defn'
      -- build up the class metadata as a list of links to the def metadata
      classMeta := classMeta.push (.link (<- storeMeta meta'))
    -- make sure we have no empty classes and all defs in a class are equal
    match classData.toList with
      | [] => throw (.badMutualBlock defs)
      | [x] => data := data.push x
      | x::xs =>
        if xs.foldr (fun y acc => (y == x) && acc) true
        then data := data.push x
        else throw (.badMutualBlock defs)
    -- build up the block metadata as a list of links to the class metadata
    meta := meta.push (.link (<- storeMeta ⟨classMeta.toList⟩))
  pure (.defs data.toList, .meta ⟨meta.toList⟩)

partial def compileDefs: PreDef -> CompileM (Ixon × Ixon)
| d => do
  let all: Set Lean.Name <- getAll d.name
  if all == {d.name} then do
    let (data, meta) <- withMutCtx {(d.name,0)} <| compileDef d
    pure (.defn data, .meta meta)
  else do
    let mut defs : Array PreDef := #[]
    for name in all do
      match <- findLeanConst name with
      | .defnInfo x => defs := defs.push (mkPreDef x)
      | .opaqueInfo x => defs := defs.push (mkPreOpaque x)
      | .thmInfo x => defs := defs.push (mkPreTheorem x)
      | x => throw $ .invalidConstantKind x.name "mutdef" x.ctorName
    let mutDefs <- sortDefs defs.toList
    let mutCtx := defMutCtx mutDefs
    let (data, meta) <- withMutCtx mutCtx <| compileMutDefs mutDefs
    -- add top-level mutual block to our state
    let block := ⟨<- storeIxon data, <- storeIxon meta⟩
    modify fun stt => { stt with blocks := stt.blocks.insert block () }
    -- then add all the projections, returning the def we started with
    let mut ret? : Option (Ixon × Ixon) := none
    for name in all do
      let idx <- do match mutCtx.find? name with
      | some idx => pure idx
      | none => throw $ .cantFindMutDefIndex name
      let data := .dprj ⟨idx, block.data⟩
      let meta := .meta ⟨[.link block.meta]⟩
      let addr := ⟨<- storeIxon data, <- storeIxon meta⟩
      modify fun stt => { stt with
        constCache := stt.constCache.insert name addr
      }
      if name == d.name then ret? := some (data, meta)
    match ret? with
    | some ret => return ret
    | none => throw $ .compileMutualBlockMissingProjection d.name

/--
`sortDefs` recursively sorts a list of mutually referential definitions into
ordered equivalence classes. For most cases equivalence can be determined by
syntactic differences in the definitions, but when two definitions
refer to one another in the same syntactical position the classification can
be self-referential. Therefore we use a partition refinement algorithm that
starts by assuming that all definitions in the mutual block are equal and
recursively improves our classification by sorting based on syntax:

```
classes₀ := [startDefs]
classes₁ := sortDefs classes₀
classes₂ := sortDefs classes₁
classes₍ᵢ₊₁₎ := sortDefs classesᵢ ...
```
Eventually we reach a fixed-point where `classes₍ᵢ₊₁₎ := classesᵢ` and no
further refinement is possible (trivially when each def is in its own class). --/
partial def sortDefs (classes: List PreDef) : CompileM (List (List PreDef)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List PreDef)): CompileM (List (List PreDef)) := do
      --dbg_trace "sortDefs blocks {(<- get).blocks.size} {(<- read).current}"
      let ctx := defMutCtx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .badMutualBlock cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareDef ctx) >>= List.groupByM (eqDef ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'

/-- AST comparison of two Lean definitions. --/
partial def compareDef (ctx: MutCtx) (x y: PreDef)
  : CompileM Ordering := do
  --dbg_trace "compareDefs constCmp {(<- get).constCmp.size} {(<- read).current}"
  let key := match compare x.name y.name with
    | .lt => (x.name, y.name)
    | _ => (y.name, x.name)
  match (<- get).constCmp.find? key with
  | some o => return o
  | none => do
    let sorder <- SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type)
        (compareExpr ctx x.levelParams y.levelParams x.value y.value)
    if sorder.strong then modify fun stt => { stt with
        constCmp := stt.constCmp.insert key sorder.ord
      }
    return sorder.ord

partial def eqDef (ctx: MutCtx) (x y: PreDef) : CompileM Bool :=
  (fun o => o == .eq) <$> compareDef ctx x y

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
        let x' <- compileConst $ ← findLeanConst x
        let y' <- compileConst $ ← findLeanConst y
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
  | .proj _ nx tx, .proj _ ny ty => 
    SOrder.cmpM (pure ⟨true, compare nx ny⟩) 
      (compareExpr ctx xlvls ylvls tx ty)

partial def mkPreInd (i: Lean.InductiveVal) : CompileM Ix.PreInd := do
  let ctors <- i.ctors.mapM getCtor
  --let recrs := (<- get).env.constants.fold getRecrs []
  return ⟨i.name, i.levelParams, i.type, i.numParams, i.numIndices, i.all,
    ctors, i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩
  where
    getCtor (name: Lean.Name) : CompileM (Lean.ConstructorVal) := do
      match (<- findLeanConst name) with
      | .ctorInfo c => pure c
      | _ => throw <| .invalidConstantKind name "constructor" ""

partial def compileConstructor: Lean.ConstructorVal -> CompileM (Ixon.Constructor × Address)
| c => withLevels c.levelParams <| do
  let n <- compileName c.name
  let ls <- c.levelParams.mapM compileName
  let t <- compileExpr c.type
  let data := ⟨c.isUnsafe, ls.length, c.cidx, c.numParams, c.numFields, t.data⟩
  let meta <- storeMeta ⟨[.link n, .links ls, .link t.meta]⟩
  pure (data, meta)

partial def compileInd: PreInd -> CompileM (Ixon.Inductive × Ixon.Metadata)
| ⟨name, lvls, type, ps, is, all, ctors, nest, rcr, refl, usafe⟩ =>
  withLevels lvls do 
  let n <- compileName name
  let ls <- lvls.mapM compileName
  let t <- compileExpr type
  --let rs <- recrs.mapM compileRecursor
  let cs <- ctors.mapM compileConstructor
  let as <- all.mapM compileName
  let data := ⟨rcr, refl, usafe, ls.length, ps, is, nest, t.data,
    cs.map (·.1)⟩
  let meta := ⟨[.link n, .links ls, .link t.meta,
    .links (cs.map (·.2)), .links as]⟩
  pure (data, meta)

partial def compileMutInds : List (List PreInd) -> CompileM (Ixon × Ixon)
| inds => do
  let mut data := #[]
  let mut meta := #[]
  -- iterate through each equivalence class
  for indsClass in inds do
    let mut classData := #[]
    let mut classMeta := #[]
    -- dematerialize each inductive in a class
    for indc in indsClass do
      let (indc', meta') <- compileInd indc
      classData := classData.push indc'
      -- build up the class metadata as a list of links to the indc metadata
      classMeta := classMeta.push (.link (<- storeMeta meta'))
    -- make sure we have no empty classes and all defs in a class are equal
    match classData.toList with
      | [] => throw (.badInductiveBlock inds)
      | [x] => data := data.push x
      | x::xs =>
        if xs.foldr (fun y acc => (y == x) && acc) true
        then data := data.push x
        else throw (.badInductiveBlock inds)
    -- build up the block metadata as a list of links to the class metadata
    meta := meta.push (.link (<- storeMeta ⟨classMeta.toList⟩))
  pure (.inds data.toList, .meta ⟨meta.toList⟩)

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the complexity of this function.
-/
partial def compileInds: PreInd -> CompileM (Ixon × Ixon)
| ind => do
  let all: Set Lean.Name <- getAll ind.name
  let mut inds := #[]
  let mut ctorNames : Map Lean.Name (List Lean.Name) := {}
  -- collect all mutual inductives as Ix.PreInds
  for n in all do
    match <- findLeanConst n with
    | .inductInfo val =>
      let ind <- mkPreInd val
      inds := inds.push ind
      ctorNames := ctorNames.insert n val.ctors
    | _ => continue
  -- sort PreInds into equivalence classes
  let mutInds <- sortInds inds.toList
  let mutCtx := indMutCtx mutInds
  -- compile each preinductive with the mutCtx
  let (data, meta) <- withMutCtx mutCtx <| compileMutInds mutInds
  -- add top-level mutual block to our state
  let block := ⟨<- storeIxon data, <- storeIxon meta⟩
  modify fun stt => { stt with blocks := stt.blocks.insert block () }
  -- then add all projections, returning the inductive we started with
  let mut ret? : Option (Ixon × Ixon) := none
  for (ind', idx) in inds.zipIdx do
    let n <- compileName ind'.name
    let data := .iprj ⟨idx, block.data⟩
    let meta := .meta ⟨[.link n, .link block.meta]⟩
    let addr := ⟨<- storeIxon data, <- storeIxon meta⟩
    modify fun stt => { stt with
      constCache := stt.constCache.insert ind'.name addr
    }
    if ind'.name == ind.name then ret? := some (data, meta)
    let some ctors := ctorNames.find? ind.name
      | throw $ .cantFindMutDefIndex ind.name
    for (cname, cidx) in ctors.zipIdx do
      let cn <- compileName cname
      let cdata := .cprj ⟨idx, cidx, block.data⟩
      let cmeta := .meta ⟨[.link cn, .link block.meta]⟩
      let caddr := ⟨<- storeIxon cdata, <- storeIxon cmeta⟩
      modify fun stt => { stt with
        constCache := stt.constCache.insert cname caddr
      }
    --for (rname, ridx) in recrs.zipIdx do
    --  let rn <- compileName rname
    --  let rdata := .rprj ⟨idx, ridx, block.data⟩
    --  let rmeta := .meta ⟨[.link rn, .link block.meta]⟩
    --  let raddr := ⟨<- storeIxon rdata, <- storeIxon rmeta⟩
    --  modify fun stt => { stt with
    --    constCache := stt.constCache.insert rname raddr
    --  }
  match ret? with
  | some ret => return ret
  | none => throw $ .compileInductiveBlockMissingProjection ind.name

/-- AST comparison of two Lean inductives. --/
partial def compareInd (ctx: MutCtx) (x y: PreInd) 
  : CompileM Ordering := do
  --dbg_trace "compareInd constCmp {(<- get).constCmp.size} {(<- read).current}"
  let key := match compare x.name y.name with
    | .lt => (x.name, y.name)
    | _ => (y.name, x.name)
  match (<- get).constCmp.find? key with
  | some o => return o
  | none => do
    let sorder <- do
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.ctors.length y.ctors.length⟩) <|
      --SOrder.cmpM (pure ⟨true, compare x.recrs.length y.recrs.length⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
      (SOrder.zipM compareCtor x.ctors y.ctors)
      --SOrder.cmpM (SOrder.zipM compareCtor x.ctors y.ctors)
      --  (SOrder.zipM compareRecr x.recrs y.recrs)
    if sorder.strong then modify fun stt => { stt with
        constCmp := stt.constCmp.insert key sorder.ord
    }
    return sorder.ord
  where
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

partial def eqInd (ctx: MutCtx) (x y: PreInd) : CompileM Bool :=
  (fun o => o == .eq) <$> compareInd ctx x y

/-- `sortInds` recursively sorts a list of inductive datatypes into equivalence
classes, analogous to `sortDefs` --/
partial def sortInds (classes : List PreInd) : CompileM (List (List PreInd)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List PreInd)): CompileM (List (List PreInd)) := do
      --dbg_trace "sortInds blocks {(<- get).blocks.size} {(<- read).current}"
      let ctx := indMutCtx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .badInductiveBlock cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareInd ctx) >>= List.groupByM (eqInd ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'

/-- AST comparison of two Lean inductives. --/
partial def compareRec (ctx: MutCtx) (x y: Lean.RecursorVal) 
  : CompileM Ordering := do
  let key := match compare x.name y.name with
    | .lt => (x.name, y.name)
    | _ => (y.name, x.name)
  match (<- get).constCmp.find? key with
  | some o => return o
  | none => do
    let sorder <- do
      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numParams y.numParams⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numIndices y.numIndices⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numMotives y.numMotives⟩) <|
      SOrder.cmpM (pure ⟨true,compare x.numMinors y.numMinors⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.k y.k⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
        (SOrder.zipM (compareRule x.levelParams y.levelParams) x.rules y.rules)
    if sorder.strong then modify fun stt => { stt with
        constCmp := stt.constCmp.insert key sorder.ord
      }
    return sorder.ord
  where
    compareRule (xlvls ylvls: List Lean.Name) (x y: Lean.RecursorRule)
      : CompileM SOrder := do
        SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩)
          (compareExpr ctx xlvls ylvls x.rhs y.rhs)

partial def eqRec (ctx: MutCtx) (x y: Lean.RecursorVal) : CompileM Bool :=
  (fun o => o == .eq) <$> compareRec ctx x y

/-- `sortRecs` recursively sorts a list of inductive recursors into equivalence
classes, analogous to `sortDefs` --/
partial def sortRecs (classes : List Lean.RecursorVal)
  : CompileM (List (List Lean.RecursorVal)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List Lean.RecursorVal)): CompileM (List (List Lean.RecursorVal)) := do
      --dbg_trace "sortInds blocks {(<- get).blocks.size} {(<- read).current}"
      let ctx := recMutCtx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .badRecursorBlock cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareRec ctx) >>= List.groupByM (eqRec ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'

partial def compileRule: Lean.RecursorRule -> CompileM (Ixon.RecursorRule × (Address × Address))
| r => do
  let n <- compileName r.ctor
  let rhs <- compileExpr r.rhs
  pure (⟨r.nfields, rhs.data⟩, (n, rhs.meta))

partial def compileRec: Lean.RecursorVal -> CompileM (Ixon.Recursor × Metadata)
| r => withLevels r.levelParams <| do
  let n <- compileName r.name
  let ls <- r.levelParams.mapM compileName
  let t <- compileExpr r.type
  let rules <- r.rules.mapM compileRule
  let data := ⟨r.k, r.isUnsafe, ls.length, r.numParams, r.numIndices,
    r.numMotives, r.numMinors, t.data, rules.map (·.1)⟩
  let meta := ⟨[.link n, .links ls, .rules (rules.map (·.2))]⟩
  pure (data, meta)

partial def compileMutRecs: List (List Lean.RecursorVal) -> CompileM (Ixon × Ixon)
| recs => do
  let mut data := #[]
  let mut meta := #[]
  -- iterate through each equivalence class
  for recsClass in recs do
    let mut classData := #[]
    let mut classMeta := #[]
    -- compile each def in a class
    for recr in recsClass do
      let (recr', meta') <- compileRec recr
      classData := classData.push recr'
      -- build up the class metadata as a list of links to the def metadata
      classMeta := classMeta.push (.link (<- storeMeta meta'))
    -- make sure we have no empty classes and all defs in a class are equal
    match classData.toList with
      | [] => throw (.badRecursorBlock recs)
      | [x] => data := data.push x
      | x::xs =>
        if xs.foldr (fun y acc => (y == x) && acc) true
        then data := data.push x
        else throw (.badRecursorBlock recs)
    -- build up the block metadata as a list of links to the class metadata
    meta := meta.push (.link (<- storeMeta ⟨classMeta.toList⟩))
  pure (.recs data.toList, .meta ⟨meta.toList⟩)

partial def compileRecs : Lean.RecursorVal -> CompileM (Ixon × Ixon)
| r => do
  let all: Set Lean.Name <- getAll r.name
  let mut recs : Array Lean.RecursorVal := #[]
  for name in all do
    match <- findLeanConst name with
    | .recInfo val => recs := recs.push val
    | x => throw $ .invalidConstantKind x.name "recursor" x.ctorName
  let mutRecs <- sortRecs recs.toList
  let mutCtx := recMutCtx mutRecs
  let (data, meta) <- withMutCtx mutCtx <| compileMutRecs mutRecs
  let block := ⟨<- storeIxon data, <- storeIxon meta⟩
  modify fun stt => { stt with blocks := stt.blocks.insert block () }
  let mut ret? : Option (Ixon × Ixon) := none
  for recr in recs do
    let idx <- do match mutCtx.find? recr.name with
    | some idx => pure idx
    | none => throw $ .cantFindMutDefIndex recr.name
    let data := .rprj ⟨idx, block.data⟩
    let meta := .meta ⟨[.link block.meta]⟩
    let addr := ⟨<- storeIxon data, <- storeIxon meta⟩
    modify fun stt => { stt with
      constCache := stt.constCache.insert recr.name addr
    }
    if recr.name == r.name then ret? := some (data, meta)
  match ret? with
  | some ret => return ret
  | none => throw $ .compileMutualBlockMissingProjection r.name

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
  let anonAddr <- compileConst anon
  let name := anonAddr.data.toUniqueName
  let const := .defnInfo ⟨⟨name, lvls, typ⟩, val, .opaque, .safe, []⟩
  let addr <- compileConst const
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
  : CompileM Unit := delta.forM fun _ c => discard $ compileConst c

def compileEnv (env: Lean.Environment)
  : CompileM Unit := do
  compileDelta env.getDelta
  env.getConstMap.forM fun _ c => if !c.isUnsafe then discard $ compileConst c else pure ()

def CompileM.runIO (c : CompileM α) 
  (env: Lean.Environment)
  (maxHeartBeats: USize := 200000)
  (seed : Option Nat := .none)
  : IO (α × CompileState) := do
  let seed <- match seed with
    | .none => IO.monoNanosNow
    | .some s => pure s
  match <- c.run .init (.init env seed maxHeartBeats) with
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
