import Std.Data.HashMap
import Ix.Ixon
import Ix.Common
import Ix.Store
import Ix.CompileM
import Init.Data.List.Control

open Ix.CompileM
open Ixon hiding Substring

namespace Ix

/- the current Ix constant being decompiled -/
structure Named where
  name: Lean.Name
  addr: MetaAddress
deriving Inhabited, Repr

instance : ToString Named where
  toString n := s!"{n.addr}.{n.name}"

/- The local environment for the Ix -> Lean4 decompiler -/
structure DecompileEnv where
  names : Map Lean.Name MetaAddress
  store : Map Address ByteArray
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  mutCtx  : Std.HashMap Lean.Name Nat
  current : Named
  deriving Repr, Inhabited

/- initialize from an Ixon store and a name-index to the store -/
def DecompileEnv.init
  (names : Map Lean.Name MetaAddress)
  (store : Map Address ByteArray)
  : DecompileEnv
  := ⟨names, store, default, default, default, default⟩

/- A Block is one of the possible sets of Lean constants we could generate
 from a pair of content and metadata Ix addresses -/
inductive Block where
| prim : Block
| defn : Def -> Block
| recr : Lean.RecursorVal -> Block
| axio : Lean.AxiomVal -> Block
| quot : Lean.QuotVal -> Block
| muts : List (List MutConst) -> Block
deriving Repr, Inhabited, Nonempty

def Block.contains (name: Lean.Name) : Block -> Bool
| .prim => name == .mkSimple "_obj" || name == .mkSimple "_neutral" || name == .mkSimple "_unreachable"
| .defn val => val.name == name
| .recr val => val.name == name
| .axio val => val.name == name
| .quot val => val.name == name
| .muts consts => consts.any (·.any (·.contains name))

def Block.consts : Block -> Set Lean.ConstantInfo
| .prim => {}
| .defn val => {defn val}
| .recr val => {.recInfo val}
| .axio val => {.axiomInfo val}
| .quot val => {.quotInfo val}
| .muts consts => consts.foldr (fun m set => set.union (m.foldr 
    (fun m' set' => set'.union (mutConst m')) {})) {}
where
  defn: Def -> Lean.ConstantInfo
  | ⟨name, lvls, type, kind, value, hints, safety, all⟩ => match kind with
  | .«definition» => .defnInfo ⟨⟨name, lvls, type⟩, value, hints, safety, all⟩
  | .«opaque» => .opaqueInfo ⟨⟨name, lvls, type⟩, value, safety == .unsafe, all⟩
  | .«theorem» => .thmInfo ⟨⟨name, lvls, type⟩, value, all⟩
  mutConst: MutConst -> Set Lean.ConstantInfo
  | .defn d => {defn d}
  | .recr r => {.recInfo r}
  | .indc i => (Std.HashSet.ofList (.ctorInfo <$> i.ctors)).insert <|
    .inductInfo (⟨⟨i.name, i.levelParams, i.type⟩, i.numParams,
      i.numIndices, i.all, (·.name) <$> i.ctors, i.numNested, i.isRec,
      i.isReflexive, i.isUnsafe⟩)

structure DecompileState where
  constants: Map Lean.Name Lean.ConstantInfo
  constCache: Map MetaAddress (Lean.Name × Set Lean.Name)
  exprCache: Map MetaAddress Lean.Expr
  univCache: Map MetaAddress Lean.Level
  synCache: Map Address Lean.Syntax
  nameCache: Map Address Lean.Name
  deriving Inhabited

inductive DecompileError
| freeLevel (curr: Named) (ctx: List Lean.Name) (lvl: Lean.Name) (idx: Nat)
| mismatchedLevelName
  (curr: Named) (ctx: List Lean.Name) (got: Lean.Name)
  (exp: Lean.Name) (idx: Nat)
| mismatchedName (curr: Named) (n m: Lean.Name)
| mismatchedNameSet (curr: Named) (n: Lean.Name) (ms: List Lean.Name)
| invalidBVarIndex (curr: Named) (ctx: List Lean.Name) (idx: Nat)
| mismatchedUnivArgs (curr: Named) (d m : List Address)
| mismatchedLevels (curr: Named) (n: Nat) (ls: List Address)
| mismatchedRules (curr: Named) (rs: List RecursorRule) (ms: List (Address × Address))
| mismatchedCtors (curr: Named) (cs: List Constructor) (ms: List Address)
| mismatchedMutIdx
  (curr: Named) (ctx: Std.HashMap Lean.Name Nat) (exp: Lean.Name) 
  (idx: Nat) (got: Nat)
| unknownMutual 
  (curr: Named) (ctx: Std.HashMap Lean.Name Nat) (exp: Lean.Name) (idx: Nat)
--| transport (curr: Named) (err: TransportError) (cont meta: Address)
--| unknownName (curr: Named) (name: Lean.Name)
| badDeserialization (addr: Address) (exp: String) (str: String)
| unknownStoreAddress (curr: Named) (addr: Address)
| badName (curr: Named) (ixon: Ixon)
| badLevel (curr: Named) (data «meta»: Ixon)
| badKVMap (curr: Named) (ixon: Ixon)
| badKVMapMetadatum (curr: Named) («meta»: Metadatum)
| badExpr (curr: Named) (data «meta»: Ixon)
| badDef (curr: Named) (d: Ixon.Definition) («meta»: Metadata)
| badRecr (curr: Named) (d: Ixon.Recursor) («meta»: Metadata)
| badCtor (curr: Named) (ctor: Ixon.Constructor) («meta»: Ixon)
| badIndc (curr: Named) (ctor: Ixon.Inductive) («meta»: Metadata)
| badMuts (curr: Named) (data «meta»: Ixon)
| badConst (curr: Named) (data «meta»: Ixon)
| badProj (curr: Named) (block: Block) (msg: String)
| badProjMeta (curr: Named) («meta»: Ixon) (msg: String)
| badCache (name: Lean.Name) (set: Set Lean.Name)
--| expectedIxonMetadata (curr: Named) (exp: Address) (got: Ixon)
--| badProjection
--  (curr: Named) (name: Lean.Name) (cont meta: Address) (msg: String)
--| nonCongruentInductives (curr: Named) (x y: Ix.Inductive)
--| nameNotInBlockNames
--  (curr: Named) (block: BlockNames) (name: Lean.Name) (cont meta: Address)
--| nameNotInBlock
--  (curr: Named) (block: Block) (name: Lean.Name) (cont meta: Address)
--| mismatchedName
--  (curr: Named) (exp: Lean.Name) (got: Lean.Name) (cont meta: Address)
--| expectedNameInBlock
--  (curr: Named) (exp: Lean.Name) (got: BlockNames) (cont meta: Address)
--| expectedDefnBlock (curr: Named) (exp: Lean.Name) (got: Block) (cont meta: Address)
--| expectedMutDefBlock (curr: Named) (got: BlockNames) (cont meta: Address)
--| expectedMutIndBlock (curr: Named) (got: BlockNames) (cont meta: Address)
--| expectedMutIndConst (curr: Named) (got: Ix.Const) (cont meta: Address)
--| expectedMutDefConst (curr: Named) (got: Ix.Const) (cont meta: Address)
--| overloadedConstants (curr: Named) (x y: Lean.ConstantInfo)
| todo
deriving Repr

def DecompileError.pretty : DecompileError -> String
| .freeLevel c lvls n i => s!"Free level {n} at {i} with ctx {repr lvls} @ {c}"
| .mismatchedLevelName c ctx n' n i => 
  s!"Expected level name {n} at index {i} but got {n'} with context {repr ctx} @ {c}"
| .mismatchedName c n m => 
  s!"Expected name {n} got {m} @ {c}"
| .mismatchedNameSet c n ms => 
  s!"Expected name {n} in {ms} @ {c}"
| .invalidBVarIndex c ctx i => 
  s!"Bound variable {i} escapes context {ctx} @ {c}"
| .mismatchedUnivArgs c d m => s!"mismatched univ args in {repr d} {repr m} @ {c}"
| .mismatchedLevels c n ls => s!"mismatched levels {n} {ls} @ {c}"
| .mismatchedRules c ras rms => s!"mismatched rules {repr ras} {rms} @ {c}"
| .mismatchedCtors c cs ms => s!"mismatched rules {repr cs} {ms} @ {c}"
| .mismatchedMutIdx c ctx n i i' => 
  s!"expected mutual recusion index {i} at name {n} but got {i'} with context {repr ctx} @ {c}"
| .unknownMutual c ctx n i => 
  s!"DecompileError: unknown mutual name {n} with expected index {i} with context {repr ctx} @ {c}"
--| .transport curr e c m => s!"decompiler transport error {e} at {c} {m} @ {curr}"
--| .unknownName c n => s!"unknown name {n} @ {c}"
| .badDeserialization a e s => s!"DecompileError: bad deserialization at {a}, expected {e}, error: {s}"
| .unknownStoreAddress c x => s!"DecompileError: unknown store address {x} @ {c}"
| .badName c i => s!"expected Name, got {repr i} @ {c}"
| .badLevel c d m => s!"expected Level, got {repr d} {repr m} @ {c}"
| .badKVMap c m => s!"expected KVMap, got {repr m} @ {c}"
| .badKVMapMetadatum c m => s!"expected KVMapMetadatum, got {repr m} @ {c}"
| .badExpr c d m => s!"expected Expr, got {repr d} {repr m} @ {c}"
| .badDef c d m => s!"expected Def, got {repr d} {repr m} @ {c}"
| .badRecr c d m => s!"expected Recr, got {repr d} {repr m} @ {c}"
| .badCtor c d m => s!"expected Ctor, got {repr d} {repr m} @ {c}"
| .badIndc c d m => s!"expected Indc, got {repr d} {repr m} @ {c}"
| .badMuts c d m => s!"expected Muts, got {repr d} {repr m} @ {c}"
| .badConst c d m => s!"expected const, got {repr d} {repr m} @ {c}"
| .badProj c b n => s!"bad Block projection of {repr b}, with {n} @ {c}"
| .badProjMeta c m n => s!"bad Block projection metadata {repr m} with {n} @ {c}"
| .badCache n s => s!"bad cache entry, expected {n} in {repr s}"
--| .expectedIxonMetadata c x ixon => s!"expected metadata at address {x}, got {repr ixon} @ {c}"
--| .badProjection curr n c m s => s!"bad projection {n} at address {c}:{m}, {s} @ {curr}"
--| .nonCongruentInductives c x y  => s!"noncongruent inductives {repr x} {repr y} @ {c}"
--| .nameNotInBlockNames curr b n c m  => s!"expected block names {repr b} at {c}:{m} to contain {n} @ {curr}"
--| .nameNotInBlock curr b n c m  => s!"expected block {repr b} at {c}:{m} to contain {n} @ {curr}"
--| .mismatchedName curr e g c m => 
--  s!"expected name {e}, got {g} at address {c} {m} @ {curr}"
--| .expectedNameInBlock curr e b c m => 
--  s!"expected name {e} in block {repr b} at address {c} {m} @ {curr}"
--| .expectedDefnBlock curr e g c m =>
--  s!"expected definition named {e}, got {repr g} at address {c} {m} @ {curr}"
--| .expectedMutDefBlock curr g c m =>
--  s!"expected mutual definition block, got {repr g} at address {c} {m} @ {curr}"
--| .expectedMutIndBlock curr g c m =>
--  s!"expected mutual inductive block, got {repr g} at address {c} {m} @ {curr}"
--| .expectedMutIndConst curr g c m =>
--  s!"expected mutual inductive constant, got {repr g} at address {c} {m} @ {curr}"
--| .expectedMutDefConst curr g c m =>
--  s!"expected mutual definition constant, got {repr g} at address {c} {m} @ {curr}"
--| .overloadedConstants curr x y => 
--  s!"overloaded constants, tried to overwrite {repr y} with {repr x} @ {curr}"
| .todo => s!"todo"

abbrev DecompileM := ReaderT DecompileEnv <| EStateM DecompileError DecompileState

def DecompileM.run (env: DecompileEnv) (stt: DecompileState) (c : DecompileM α)
  : EStateM.Result DecompileError DecompileState α
  := EStateM.run (ReaderT.run c env) stt

-- add binding name to local context
def DecompileM.withBinder (name: Lean.Name) : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def DecompileM.withLevels (lvls : List Lean.Name) : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def DecompileM.withMutCtx (mutCtx : Std.HashMap Lean.Name Nat)
  : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

def withNamed (name: Lean.Name) (cont «meta»: Address)
  : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with current := ⟨name, cont, «meta»⟩ }

-- reset local context
def DecompileM.resetCtx (name: Lean.Name) («meta»: MetaAddress) 
  : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with 
    univCtx := [], bindCtx := [], mutCtx := {}, current := ⟨name, «meta»⟩
  }

def readStore [Serialize A] (addr: Address) (exp: String): DecompileM A := do
  --dbg_trace "readStore {addr}"
  match (<- read).store.find? addr with
  | some bytes => match Ixon.de bytes with
    | .ok ixon => pure ixon
    | .error e => throw <| .badDeserialization addr exp e
  | none => throw <| .unknownStoreAddress (<- read).current addr

def readNat (addr: Address) : DecompileM Nat := do
  --dbg_trace "readNat {addr}"
  match (<- read).store.find? addr with
  | some bytes => return Nat.fromBytesLE bytes.data
  | none => throw <| .unknownStoreAddress (<- read).current addr

def readString (addr: Address): DecompileM String := do
  --dbg_trace "readString {addr}"
  match (<- read).store.find? addr with
  | some bytes => match String.fromUTF8? bytes with
    | .some s => pure s
    | .none => throw <| .badDeserialization addr "UTF8" ""
  | none => throw <| .unknownStoreAddress (<- read).current addr

def readIxon (addr: Address) : DecompileM Ixon := do
  --dbg_trace "readIxon {addr}"
  match (<- read).store.find? addr with
  | some bytes => match Ixon.de bytes with
    | .ok ixon => pure ixon
    | .error e => throw <| .badDeserialization addr "Ixon" e
  | none => throw <| .unknownStoreAddress (<- read).current addr

partial def decompileName (addr: Address) : DecompileM Lean.Name := do
  match (<- get).nameCache.find? addr with
  | some name => 
  --dbg_trace "decompileName {(<- read).current.name} {addr} {name}"
    pure name
  | none => do
    let name <- go (<- readIxon addr)
  --dbg_trace "decompileName {(<- read).current.name} {addr} {name}"
    modifyGet fun stt => (name, { stt with
      nameCache := stt.nameCache.insert addr name
    })
  where
    go : Ixon -> DecompileM Lean.Name
    | .nanon => return Lean.Name.anonymous
    | .nstr n s => do
       let n' <- decompileName n
       let s' <- readString s
       return Lean.Name.str n' s'
    | .nnum n i => do
       let n' <- decompileName n
       let i' <- readNat i
       return Lean.Name.num n' i'
    | ixon => do throw <| .badName (<- read).current ixon

partial def decompileLevel (addr: MetaAddress): DecompileM Lean.Level := do
  --dbg_trace s!"decompileLevel"
  match (<- get).univCache.find? addr with
  | some x => pure x
  | none => do
    let level <- go (<- readIxon addr.data) (<- readIxon addr.meta)
    modifyGet fun stt => (level, { stt with
      univCache := stt.univCache.insert addr level
    })
  where
    go : Ixon -> Ixon -> DecompileM Lean.Level
    | .uzero, .meta ⟨[]⟩ => return .zero
    | .usucc a, .meta ⟨[.link m]⟩ => do
      let x <- decompileLevel ⟨a, m⟩
      return .succ x
    | .umax xa ya, .meta ⟨[.link xm, .link ym]⟩ => do
      let x <- decompileLevel ⟨xa, xm⟩
      let y <- decompileLevel ⟨ya, ym⟩
      return .max x y
    | .uimax xa ya, .meta ⟨[.link xm, .link ym]⟩ => do
      let x <- decompileLevel ⟨xa, xm⟩
      let y <- decompileLevel ⟨ya, ym⟩
      return .imax x y
    | .uvar i, .meta ⟨[.link n]⟩ => do
      let name <- decompileName n
      match (<- read).univCtx[i]? with
      | some name' => do
        if name' == name then pure (.param name)
        else throw <| .mismatchedLevelName (<- read).current (<- read).univCtx name name' i
      | none => do throw <| .freeLevel (<- read).current (<- read).univCtx name i
    | d , m => do throw <| .badLevel (<- read).current d m

def decompileSubstring : Ixon.Substring -> DecompileM Substring
| ⟨s, startPos, stopPos⟩ => do pure ⟨<- readString s, ⟨startPos⟩, ⟨stopPos⟩⟩

def decompileSourceInfo : Ixon.SourceInfo -> DecompileM Lean.SourceInfo
| .original l p t e => do
  let l' <- decompileSubstring l
  let t' <- decompileSubstring t
  pure <| .original l' ⟨p⟩ t' ⟨e⟩
| .synthetic p e c => pure <| .synthetic ⟨p⟩ ⟨e⟩ c
| .none => pure .none

def decompilePreresolved : Ixon.Preresolved -> DecompileM Lean.Syntax.Preresolved
| .namespace ns => .namespace <$> decompileName ns
| .decl n fs => .decl <$> decompileName n <*> (fs.mapM readString)

partial def decompileSyntax (addr: Address): DecompileM Lean.Syntax := do
  match (<- get).synCache.find? addr with
  | some x => pure x
  | none => do
    let syn' <- go (<- readStore addr "Syntax")
    modifyGet fun stt => (syn', { stt with
      synCache := stt.synCache.insert addr syn'
    })
  where
    go : Ixon.Syntax -> DecompileM Lean.Syntax
    | .missing => pure .missing
    | .node info kind args => do
      let info' <- decompileSourceInfo info
      let kind' <- decompileName kind
      let args' <- args.mapM decompileSyntax
      pure <| .node info' kind' ⟨args'⟩
    | .atom info val => do
      let info' <- decompileSourceInfo info
      let val' <- readString val
      pure <| .atom info' val'
    | .ident info rawVal val preresolved => do
      let info' <- decompileSourceInfo info
      let rawVal' <- decompileSubstring rawVal
      let val' <- decompileName val
      let ps' <- preresolved.mapM decompilePreresolved
      pure <| .ident info' rawVal' val' ps'

partial def decompileDataValue: Ixon.DataValue -> DecompileM Lean.DataValue
| .ofString s => .ofString <$> readString s
| .ofBool b => pure (.ofBool b)
| .ofName n => .ofName <$> decompileName n
| .ofNat i => .ofNat <$> readNat i
| .ofInt i => .ofInt <$> readStore i "Int"
| .ofSyntax s => .ofSyntax <$> (decompileSyntax s)

partial def decompileKVMaps (addr: Address) : DecompileM (List Lean.KVMap) := do
  match (<- readIxon addr) with
  | .meta ⟨ms⟩ => ms.mapM go
  | x => throw <| .badKVMap (<- read).current x
  where
    go : Metadatum -> DecompileM Lean.KVMap
    | .kvmap xs => do
      let mut kv := {}
      for (n, d) in xs do
        let n <- decompileName n
        let d <- decompileDataValue d
        kv := kv.insert n d
      return kv
    | x => do throw <| .badKVMapMetadatum (<- read).current x

partial def insertBlock (block: Block): DecompileM (Set Lean.Name) := do
  let mut set := {}
  for c in block.consts do
    modify fun stt => { stt with constants := stt.constants.insert c.name c }
    set := set.insert c.name
  return set

def namesEqPatch (x y: Lean.Name) : Bool :=
  let cs2 := Lean.Name.mkSimple "_cstage2"
  x == y || x == y.append cs2  || x.append cs2 == y

def matchNames (x y: Lean.Name) : DecompileM α -> DecompileM α
| a => do
  if namesEqPatch x y then a
  else throw <| .mismatchedName (<- read).current x y

partial def matchBlock (n: Lean.Name) (idx: Nat) (block: Block)
  : DecompileM MutConst := go block
  where
    go : Block -> DecompileM MutConst
    | .muts mss => match mss[idx]? with
      | .some ms => match ms.find? (fun m => namesEqPatch n m.name) with
        | .some m => return m
        | .none => do throw <| .todo
      | .none => do throw <| .todo
    | _ => do throw <| .todo

mutual

partial def decompileExpr (addr: MetaAddress): DecompileM Lean.Expr := do
  --dbg_trace s!"decompileExpr {addr}"
  match (<- get).exprCache.find? addr with
  | some x => pure x
  | none => do
    let level <- go (<- readIxon addr.data) (<- readIxon addr.meta)
    modifyGet fun stt => (level, { stt with
      exprCache := stt.exprCache.insert addr level
    })
  where
    mdata : List Lean.KVMap -> Lean.Expr -> Lean.Expr
    | [], x => x
    | kv::kvs, x => .mdata kv (mdata kvs x)
    univs (as ms: List Address): DecompileM (List Lean.Level) := do
      if as.length != ms.length
      then throw <| .mismatchedUnivArgs (<- read).current as ms
      else (as.zip ms).mapM fun (ua, um) => decompileLevel ⟨ua, um⟩
    go : Ixon -> Ixon -> DecompileM Lean.Expr
    | .evar i, .meta ⟨[.link md]⟩ => do
      --dbg_trace s!"decompileExpr evar"
      let kvs <- decompileKVMaps md
      match (<- read).bindCtx[i]? with
      | some _ => return mdata kvs (.bvar i)
      | none => throw <| .invalidBVarIndex (<-read).current (<-read).bindCtx i
    | .esort ua, .meta ⟨[.link md, .link um]⟩ => do
      --dbg_trace s!"decompileExpr esort"
      let kvs <- decompileKVMaps md
      let u <- decompileLevel ⟨ua, um⟩
      return mdata kvs (.sort u)
    | .erec idx uas, .meta ⟨[.link md, .link n, .links ums]⟩ => do
      let kvs <- decompileKVMaps md
      let us <- univs uas ums
      let name <- decompileName n
    --dbg_trace s!"decompileExpr {(<- read).current} erec {idx} {name}, md: {md}, us: {repr us}, n: {n}"
      match (<- read).mutCtx.get? name with
      | some idx' => do
        if idx' == idx then return mdata kvs (.const name us)
        else throw <| .mismatchedMutIdx (<- read).current (<- read).mutCtx name idx idx'
      | none => do throw <| .unknownMutual (<- read).current (<- read).mutCtx name idx
    | .eref rd uas, .meta ⟨[.link md, .link n, .link rm, .links ums]⟩ => do
      let name <- decompileName n
    --dbg_trace s!"decompileExpr {(<- read).current} eref {name}"
      let kvs <- decompileKVMaps md
      let us <- univs uas ums
      let (name', _) <- decompileNamedConst name ⟨rd, rm⟩
      return mdata kvs (.const name' us)
    | .eapp fa aa, .meta ⟨[.link md, .link fm, .link am]⟩ => do
      --dbg_trace s!"decompileExpr eapp"
      let kvs <- decompileKVMaps md
      let f <- decompileExpr ⟨fa, fm⟩
      let a <- decompileExpr ⟨aa, am⟩
      return mdata kvs (.app f a)
    | .elam ta ba, .meta ⟨[.link md, .link n, .info i, .link tm, .link bm]⟩ => do
      --dbg_trace s!"decompileExpr elam"
      let name <- decompileName n
      let kvs <- decompileKVMaps md
      let t <- decompileExpr ⟨ta, tm⟩
      let b <- .withBinder name (decompileExpr ⟨ba, bm⟩)
      return mdata kvs (.lam name t b i)
    | .eall ta ba, .meta ⟨[.link md, .link n, .info i, .link tm, .link bm]⟩ => do
      --dbg_trace s!"decompileExpr eall"
      let name <- decompileName n
      let kvs <- decompileKVMaps md
      let t <- decompileExpr ⟨ta, tm⟩
      let b <- .withBinder name (decompileExpr ⟨ba, bm⟩)
      return mdata kvs (.forallE name t b i)
    | .elet nD ta va ba, .meta ⟨[.link md, .link n, .link tm, .link vm, .link bm]⟩ => do
      --dbg_trace s!"decompileExpr elet"
      let name <- decompileName n
      let kvs <- decompileKVMaps md
      let t <- decompileExpr ⟨ta, tm⟩
      let v <- decompileExpr ⟨va, vm⟩
      let b <- .withBinder name (decompileExpr ⟨ba, bm⟩)
      return mdata kvs (.letE name t v b nD)
    | .enat n, .meta ⟨[.link md]⟩ => do
      --dbg_trace s!"decompileExpr enat"
      let kvs <- decompileKVMaps md
      let n <- readNat n
      return mdata kvs (.lit (.natVal n))
    | .estr n, .meta ⟨[.link md]⟩ => do
      --dbg_trace s!"decompileExpr estr"
      let kvs <- decompileKVMaps md
      let n <- readString n
      return mdata kvs (.lit (.strVal n))
    | .eprj ta idx sa, .meta ⟨[.link md, .link n, .link tm, .link sm]⟩ => do
      --dbg_trace s!"decompileExpr eprj"
      let kvs <- decompileKVMaps md
      let name <- decompileName n
      let (name', _) <- decompileNamedConst name ⟨ta, tm⟩
      let s <- decompileExpr ⟨sa, sm⟩
      return mdata kvs (.proj name' idx s)
    | d , m => do throw <| .badExpr (<- read).current d m

partial def decompileLevels (n: Nat) (ls: List Address)
  : DecompileM (List Lean.Name) := do
  --dbg_trace "decompileLevels"
  if ls.length != n then throw <| .mismatchedLevels (<- read).current n ls
  else ls.mapM decompileName

partial def decompileDef: Ixon.Definition -> Metadata -> DecompileM Def
| d, ⟨[.link n, .links ls, .hints h, .link tm, .link vm, .links as]⟩ => do
  let name <- decompileName n
--dbg_trace s!"decompileDef {(<- read).current} {name} {repr (<- read).mutCtx}"
  let lvls <- decompileLevels d.lvls ls
  .withLevels lvls <| do
    let t <- decompileExpr ⟨d.type, tm⟩
    let v <- decompileExpr ⟨d.value, vm⟩
    let all <- as.mapM decompileName
    return ⟨name, lvls, t, d.kind, v, h, d.safety, all⟩
| d, m => do throw <| .badDef (<- read).current d m

partial def decompileRules (rs: List RecursorRule) (ms: List (Address × Address))
  : DecompileM (List Lean.RecursorRule) := do
  if rs.length != ms.length
  then throw <| .mismatchedRules (<- read).current rs ms
  else (List.zip rs ms).mapM <| fun (r, n, rm) => do
    let n <- decompileName n
    let rhs <- decompileExpr ⟨r.rhs, rm⟩
    return ⟨n, r.fields, rhs⟩

partial def decompileRecr: Ixon.Recursor -> Metadata -> DecompileM Rec
| r, ⟨[.link n, .links ls, .link tm, .map rs, .links as]⟩ => do
  let name <- decompileName n
--dbg_trace s!"decompileRecr {(<- read).current} {name} {repr (<- read).mutCtx}"
  let lvls <- decompileLevels r.lvls ls
  .withLevels lvls <| do
    let t <- decompileExpr ⟨r.type, tm⟩
    let all <- as.mapM decompileName
    let rs <- decompileRules r.rules rs
    return ⟨⟨name, lvls, t⟩, all, r.params, r.indices, r.motives,
      r.minors, rs, r.k, r.isUnsafe⟩
| r, m => do throw <| .badRecr (<- read).current r m

partial def decompileCtors (cs: List Ixon.Constructor) (ms: List Address)
  : DecompileM (List Lean.ConstructorVal) := do
  if cs.length != ms.length
  then throw <| .mismatchedCtors (<- read).current cs ms
  else (List.zip cs ms).mapM <| fun (c, m) => do go c (<- readIxon m)
  where
    go : Ixon.Constructor -> Ixon -> DecompileM Lean.ConstructorVal
    | c, .meta ⟨[.link n, .links ls, .link tm, .link i]⟩ => do
      let name <- decompileName n
      let induct <- decompileName i
      let lvls <- decompileLevels c.lvls ls
      let type <- decompileExpr ⟨c.type, tm⟩
      return ⟨⟨name, lvls, type⟩, induct, c.cidx, c.params, c.fields, c.isUnsafe⟩
    | c, m => do throw <| .badCtor (<- read).current c m

partial def decompileIndc: Ixon.Inductive -> Metadata -> DecompileM Ind
| i, ⟨[.link n, .links ls, .link tm, .links cs, .links as]⟩ => do
  let name <- decompileName n
--dbg_trace s!"decompileIndc {(<- read).current} {name} {repr (<- read).mutCtx}"
  let lvls <- decompileLevels i.lvls ls
  .withLevels lvls <| do
    let t <- decompileExpr ⟨i.type, tm⟩
    let all <- as.mapM decompileName
    let ctors <- decompileCtors i.ctors cs
    return ⟨name, lvls, t, i.params, i.indices, all, ctors,
      i.nested, i.recr, i.refl, i.isUnsafe⟩
| i, m => do throw <| .badIndc (<- read).current i m

partial def decompileConst (addr: MetaAddress)
  : DecompileM (Lean.Name × Set Lean.Name) := do
--dbg_trace s!"decompileConst {(<- read).current} {addr} {repr (<- read).mutCtx}"
  match (<- get).constCache.find? addr with
  | some x => pure x
  | none => do
    let (name, block) <- go (<- readIxon addr.data) (<- readIxon addr.meta)
    let blockNames <- insertBlock block
    modifyGet fun stt => ((name, blockNames), { stt with
      constCache := stt.constCache.insert addr (name, blockNames)
    })
  where
    go : Ixon -> Ixon -> DecompileM (Lean.Name × Block)
    | .defn d, .meta m@⟨(.link n)::_⟩ => do
      --dbg_trace s!"decompileConst defn"
      let name <- decompileName n
      let d <- .withMutCtx {(name, 0)} <| decompileDef d m
      return (d.name, .defn d)
    | .axio a, .meta ⟨[.link n, .links ls, .link tm]⟩ => do
      --dbg_trace s!"decompileConst axio"
      let name <- decompileName n
      let lvls <- decompileLevels a.lvls ls
      let t <- decompileExpr ⟨a.type, tm⟩
      return (name, .axio ⟨⟨name, lvls, t⟩, a.isUnsafe⟩)
    | .quot q, .meta ⟨[.link n, .links ls, .link tm]⟩ => do
      --dbg_trace s!"decompileConst quot"
      let name <- decompileName n
      let lvls <- decompileLevels q.lvls ls
      let t <- decompileExpr ⟨q.type, tm⟩
      return (name, .quot ⟨⟨name, lvls, t⟩, q.kind⟩)
    | .recr r, .meta m@⟨(.link n)::_⟩ => do 
      --dbg_trace s!"decompileConst recr"
      let name <- decompileName n
      let r <- .withMutCtx {(name, 0)} <| decompileRecr r m
      return (r.name, .recr r)
    | .dprj ⟨idx, bd⟩, .meta ⟨[.link bm, .link m]⟩ => do
      match (<- readIxon m) with
      | .meta ⟨[.link n, .links _, .hints _, .link _, .link _, .links _]⟩ => do
        let name <- decompileName n
        let block <- decompileMuts (<- readIxon bd) (<- readIxon bm)
        match (<- matchBlock name idx block) with
        | .defn _ => pure (name, block)
        | e => throw <| .badProj (<- read).current block s!"malformed dprj at {idx} of {repr e}"
      | m => do throw <| .badProjMeta (<- read).current m "dprj"
    | .rprj ⟨idx, bd⟩, .meta ⟨[.link bm, .link m]⟩ => do
      match (<- readIxon m) with
      | .meta ⟨[.link n, .links _, .link _, .map _, .links _]⟩ => do
        let name <- decompileName n
        let block <- decompileMuts (<- readIxon bd) (<- readIxon bm)
        match (<- matchBlock name idx block) with
        | .recr _ => (pure (name, block))
        | e => throw <| .badProj (<- read).current block s!"malformed rprj at {idx} of {repr e}"
      | m => do throw <| .badProjMeta (<- read).current m "rprj"
    | .iprj ⟨idx, bd⟩, .meta ⟨[.link bm, .link m]⟩ => do
      match (<- readIxon m) with
      | .meta ⟨[.link n, .links _, .link _, .links _, .links _]⟩ => do
        let name <- decompileName n
        let block <- decompileMuts (<- readIxon bd) (<- readIxon bm)
        match (<- matchBlock name idx block) with
        | .indc _ => (pure (name, block))
        | e => throw <| .badProj (<- read).current block s!"malformed iprj at {idx} of {repr e}"
      | m => do throw <| .badProjMeta (<- read).current m "iprj"
    | .cprj ⟨idx, cidx, bd⟩, .meta ⟨[.link bm, .link m]⟩ => do
      match (<- readIxon m) with
      | .meta ⟨[.link n, .links _, .link _, .link i]⟩ => do
        let name <- decompileName n
        let induct <- decompileName i
        let block <- decompileMuts (<- readIxon bd) (<- readIxon bm)
        match (<- matchBlock induct idx block) with
        | .indc i => match i.ctors[cidx]? with
          | .some c => matchNames name c.name (pure (name, block))
          | .none => do throw <| .badProj (<- read).current block s!"malformed cprj ctor index {cidx}"
        | e => throw <| .badProj (<- read).current block s!"malformed cprj at {idx} of {repr e}"
      | m => do throw <| .badProjMeta (<- read).current m "cprj"
    | .prim .obj, .meta ⟨[]⟩ => do
      --dbg_trace s!"decompileConst prim _obj"
      return (.mkSimple "_obj", .prim)
    | .prim .neutral, .meta ⟨[]⟩ => do
      --dbg_trace s!"decompileConst prim _neutral"
      return (.mkSimple "_neutral", .prim)
    | .prim .unreachable, .meta ⟨[]⟩ => do
      --dbg_trace s!"decompileConst prim _unreachable"
      return (.mkSimple "_unreachable", .prim)
    | d, m => do throw <| .badConst (<- read).current d m

partial def decompileNamedConst (name: Lean.Name) (addr: MetaAddress)
  : DecompileM (Lean.Name × Set Lean.Name) := do
  --dbg_trace s!"decompileNamedConst {name} {addr}"
--dbg_trace s!"decompileNamedConst {name} {addr} {repr (<- read).mutCtx}"
  let (n, set) <- .resetCtx name addr <| decompileConst addr
  matchNames n name (pure (n, set))

partial def decompileMutConst : Ixon.MutConst -> Metadata -> DecompileM MutConst
| .defn d, m => .defn <$> decompileDef d m
| .recr r, m => .recr <$> decompileRecr r m
| .indc i, m => .indc <$> decompileIndc i m

partial def decompileMuts: Ixon -> Ixon -> DecompileM Block
| ms@(.muts cs), m@(.meta ⟨[.muts names, .map ctx, .map metaMap]⟩) => do
  --dbg_trace s!"decompileMuts {(<- read).current} {repr (<- read).mutCtx}"
    if cs.length != names.length then throw <| .badMuts (<- read).current ms m
    else
      let mut map : Map Lean.Name Metadata := {}
      for (name, «meta») in metaMap do
        map := map.insert (<- decompileName name) (<- readStore «meta» "Metadata")
      let mut mutClasses := #[]
      let mut mutCtx := {}
      for (n, i) in ctx do
        mutCtx := mutCtx.insert (<- decompileName n) (<- readNat i)
    --dbg_trace s!"decompileMuts {(<- read).current} inner mutCtx {repr mutCtx}"
      for (const, names) in cs.zip names do
        let mut mutClass := #[]
        for n in names do
          let name <- decompileName n
        --dbg_trace s!"decompileMuts {(<- read).current} inner loop {name} {repr mutCtx}"
          let const' <- match map.get? name with
            | .some «meta» => .withMutCtx mutCtx <| decompileMutConst const «meta»
            | .none => do throw <| .badMuts (<- read).current ms m
          mutClass := mutClass.push const'
        mutClasses := mutClasses.push mutClass
      return .muts (Array.toList <$> mutClasses).toList
| ms, m => do throw <| .badMuts (<- read).current ms m

end

end Ix

--def decompileEnv : DecompileM Unit := do
--  for (n, (anon, meta)) in (<- read).names do
--    let _ <- ensureBlock n anon meta
