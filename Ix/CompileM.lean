import Batteries.Data.RBMap
import Ix.Ixon
import Ix.Address
import Ix.IR
import Ix.Common
--import Ix.Store
import Ix.SOrder
import Ix.Cronos

open Batteries (RBMap)
open Batteries (RBSet)

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
  store: RBMap Address ByteArray compare
  ixonCache: RBMap Ixon Address compare
  univCache: RBMap Lean.Level Ix.Level compare
  univAddrs: RBMap Ix.Level MetaAddress compare
  constNames: RBMap Lean.Name MetaAddress compare
  constCache: RBMap Lean.ConstantInfo Ix.Const compare
  constAddrs : RBMap Ix.Const MetaAddress compare
  exprCache: RBMap Lean.Expr Ix.Expr compare
  exprAddrs: RBMap Ix.Expr MetaAddress compare
  synCache: RBMap Lean.Syntax Ixon.Syntax compare
  nameCache: RBMap Lean.Name Address compare
  strCache: RBMap String Address compare
  comms: RBMap Lean.Name MetaAddress compare
  constCmp: RBMap (Lean.Name × Lean.Name) Ordering compare
  exprCmp: RBMap (CompileEnv × Lean.Expr × Lean.Expr) Ordering compare
  axioms: RBMap Lean.Name MetaAddress compare
  blocks: RBSet MetaAddress compare
  cronos: Cronos

def CompileState.init (env: Lean.Environment) (seed: Nat) (maxHeartBeats: USize := 200000)
  : CompileState :=
  ⟨maxHeartBeats, env, mkStdGen seed, default, default, default, default,
  default, default, default, default, default, default, default, default,
  default, default, default, default, default, default⟩

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
| alphaInvarianceFailure : Ix.Const -> MetaAddress -> Ix.Const -> MetaAddress -> CompileError
| dematBadMutualBlock: MutualBlock -> CompileError
| dematBadInductiveBlock: InductiveBlock -> CompileError
| emptyDefsClass: List (List PreDef) -> CompileError
| emptyIndsClass: List (List PreInd) -> CompileError
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
| .dematBadMutualBlock block => pure s!"bad mutual block while dematerializing {repr block}"
| .dematBadInductiveBlock block => pure s!"bad mutual block while dematerializing {repr block}"
| .emptyDefsClass dss => 
  pure s!"empty equivalence class while sorting definitions {dss.map fun ds => ds.map (·.name)}"
| .emptyIndsClass dss => 
  pure s!"empty equivalence class while sorting inductives {dss.map fun ds => ds.map (·.name)}"

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
    dbg_trace "storeIxon hash {addr} {(<- read).current}"
    modifyGet fun stt => (addr, { stt with
      store := stt.store.insert addr bytes
    })

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

def storeMetadata (meta: Metadata): CompileM Address := do
  let bytes := Ixon.ser meta
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def dematerializeName (name: Lean.Name): CompileM Address := do
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
      let n' <- dematerializeName n
      let s' <- storeString s
      storeIxon (.nstr n' s')
    | .num n i => do
      let n' <- dematerializeName n
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

def dematerializeLevel (lvl: Ix.Level): CompileM MetaAddress := do
  match (<- get).univAddrs.find? lvl with
  | some l => pure l
  | none => do
    --dbg_trace "dematerializeLevel go {(<- get).univAddrs.size} {(<- read).current}"
    let (anon, meta) <- go lvl
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    modifyGet fun stt => (maddr, { stt with
      univAddrs := stt.univAddrs.insert lvl maddr
    })
  where
    go : Ix.Level -> CompileM (Ixon × Ixon)
    | .zero => pure (.uzero, .meta default)
    | .succ x => do
      let ⟨a, m⟩ <- dematerializeLevel x
      pure (.usucc a, .meta ⟨[.link m]⟩)
    | .max x y => do
      let ⟨xa, xm⟩ <- dematerializeLevel x
      let ⟨ya, ym⟩ <- dematerializeLevel y
      pure (.umax xa ya, .meta ⟨[.link xm, .link ym]⟩)
    | .imax x y => do
      let ⟨xa, xm⟩ <- dematerializeLevel x
      let ⟨ya, ym⟩ <- dematerializeLevel y
      pure (.uimax xa ya, .meta ⟨[.link xm, .link ym]⟩)
    | .param n i => do
      let n' <- dematerializeName n
      pure (.uvar i, .meta ⟨[.name n']⟩)

/-- Canonicalizes a Lean universe level --/
def compileLevel (lvl: Lean.Level): CompileM Ix.Level := do
  match (<- get).univCache.find? lvl with
  | some l => pure l
  | none => do
    --dbg_trace "compileLevel go {(<- get).univCache.size} {(<- read).current}"
    let lvl' <- go lvl
    --let _ <- dematerializeLevel lvl'
    modifyGet fun stt => (lvl', { stt with
      univCache := stt.univCache.insert lvl lvl'
    })
  where
    go : Lean.Level -> CompileM Ix.Level
    | .zero => pure .zero
    | .succ u => return .succ (← compileLevel u)
    | .max a b  => return .max (← compileLevel a) (← compileLevel b)
    | .imax a b => return .imax (← compileLevel a) (← compileLevel b)
    | .param name => do
      let lvls := (← read).univCtx
      match lvls.idxOf? name with
      | some n => pure $ .param name n
      | none   => throw $ .levelNotFound name lvls s!"compileLevel"
    | l@(.mvar ..) => throw $ .levelMetavariable l

def dematerializeExpr (expr: Ix.Expr): CompileM MetaAddress := do
  match (<- get).exprAddrs.find? expr with
  | some x => pure x
  | none => do
    --dbg_trace "dematerializeExpr go {(<- get).exprAddrs.size} {(<- read).current}"
    let (anon, meta) <- go expr
    --dbg_trace "dematerializeExpr store {(<- get).exprAddrs.size} {(<- read).current}"
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    modifyGet fun stt => (maddr, { stt with
      exprAddrs := stt.exprAddrs.insert expr maddr
    })
  where
    go : Ix.Expr -> CompileM (Ixon × Ixon)
    | .var md idx => do
      --dbg_trace "dematExpr var {(<- get).exprAddrs.size} {(<- read).current}"
      pure (.evar idx, .meta ⟨[.link md]⟩)
    | .sort md univ => do
      --dbg_trace "dematExpr sort {(<- get).exprAddrs.size} {(<- read).current}"
      let ⟨udata, umeta⟩ <- dematerializeLevel univ
      let data := .esort udata
      let meta := .meta ⟨[.link md, .link umeta]⟩
      pure (data, meta)
    | .const md name ref univs => do
      --dbg_trace "dematExpr const {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName name
      let us <- univs.mapM dematerializeLevel
      let data := .eref ref.data (us.map (·.data))
      let meta := .meta ⟨[.link md, .name n, .link ref.meta] ++ us.map (.name ·.meta)⟩
      pure (data, meta)
    | .rec_ md name idx univs => do
      --dbg_trace "dematExpr rec {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName name
      let us <- univs.mapM dematerializeLevel
      let data := .erec idx (us.map (·.data))
      let meta := .meta ⟨[.link md, .name n] ++ us.map (.name ·.meta)⟩
      pure (data, meta)
    | .app md func argm => do
      --dbg_trace "dematExpr app {(<- get).exprAddrs.size} {(<- read).current}"
      let f' <- dematerializeExpr func
      let a' <- dematerializeExpr argm
      let data := .eapp f'.data a'.data
      let meta := .meta ⟨[.link md, .link f'.meta, .link a'.meta]⟩
      pure (data, meta)
    | .lam md name info type body => do
      --dbg_trace "dematExpr lam {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let b' <- dematerializeExpr body
      let data := .elam t'.data b'.data
      let meta := .meta ⟨[.link md, .name n, .info info, .link t'.meta, .link b'.meta]⟩
      pure (data, meta)
    | .pi md name info type body => do
      --dbg_trace "dematExpr pi {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let b' <- dematerializeExpr body
      let data := .eall t'.data b'.data
      let meta := .meta ⟨[.link md, .name n, .info info, .link t'.meta, .link b'.meta]⟩
      pure (data, meta)
    | .letE md name type value body nD => do
      --dbg_trace "dematExpr letE {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let v' <- dematerializeExpr value
      let b' <- dematerializeExpr body
      let data := .elet nD t'.data v'.data b'.data
      let meta := .meta ⟨[.link md, .name n, .link t'.meta, .link v'.meta, .link b'.meta]⟩
      pure (data, meta)
    | .lit md (.natVal n) => do pure (.enat (<- storeNat n), .meta ⟨[.link md]⟩)
    | .lit md (.strVal s) => do pure (.estr (<- storeString s), .meta ⟨[.link md]⟩)
    | .proj md typeName type idx struct => do
      --dbg_trace "dematExpr proj {(<- get).exprAddrs.size} {(<- read).current}"
      let n <- dematerializeName typeName
      let s' <- dematerializeExpr struct
      let data := .eprj type.data idx s'.data
      let meta := .meta ⟨[.link md, .name n, .link type.meta, .link s'.meta]⟩
      pure (data, meta)

def dematerializeConst (const: Ix.Const): CompileM MetaAddress := do
  match (<- get).constAddrs.find? const with
  | some x => pure x
  | none => do
    let (anon, meta) <- go const
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    dbg_trace "dematerializeConst exprAddrs {(<- get).exprAddrs.size} {(<- read).current}"
    dbg_trace "dematerializeConst constAddrs {(<- get).constAddrs.size} {(<- read).current}"
    modifyGet fun stt => (maddr, { stt with
      constAddrs := stt.constAddrs.insert const maddr
    })
  where
    goDef : Ix.Definition -> CompileM (Ixon.Definition × Ixon.Metadata)
    | ⟨name, lvls, type, kind, value, hints, safety, all⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let v <- dematerializeExpr value
      let as <- storeMetadata ⟨<- all.mapM (.name <$> dematerializeName ·)⟩
      let data := ⟨kind, safety, lvls.length, t.data, v.data⟩
      let meta := ⟨[.name n, .link ls, .hints hints, .link t.meta, .link v.meta, .link as]⟩
      pure (data, meta)
    goCtor : Ix.Constructor -> CompileM (Ixon.Constructor × Ixon.Metadata)
    | ⟨name, lvls, type, cidx, params, fields, usafe⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let ctor := ⟨usafe, lvls.length, cidx, params, fields, t.data⟩
      let meta := ⟨[.name n, .link ls, .link t.meta]⟩
      pure (ctor, meta)
    goRecrRule : Ix.RecursorRule -> CompileM (Ixon.RecursorRule × Ixon.Metadata)
    | ⟨ctor, fields, rhs⟩ => do
      let c <- dematerializeName ctor
      let x <- dematerializeExpr rhs
      let rule := ⟨fields, x.data⟩
      let meta := ⟨[.name c, .link x.meta]⟩
      pure (rule, meta)
    goRecr : Ix.Recursor -> CompileM (Ixon.Recursor × Ixon.Metadata)
    | ⟨name, lvls, type, params, indices, motives, minors, rules, k, usafe⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let rules <- rules.mapM goRecrRule
      let rulesData := rules.map (·.1)
      let rulesMeta <- storeMetadata ⟨<- rules.mapM (.link <$> storeMetadata ·.2)⟩
      let recr := ⟨k, usafe, lvls.length, params, indices, motives, minors, t.data, rulesData⟩
      let meta := ⟨[.name n, .link ls, .link t.meta, .link rulesMeta]⟩
      pure (recr, meta)
    goInd : Ix.Inductive -> CompileM (Ixon.Inductive × Ixon.Metadata)
    | ⟨name, lvls, type, params, indices, all, ctors, recrs, nested, recr, refl, usafe⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let cs <- ctors.mapM goCtor
      let ctorsData := cs.map (·.1)
      let ctorsMeta <- storeMetadata ⟨<- cs.mapM (.link <$> storeMetadata ·.2)⟩
      let rs <- recrs.mapM goRecr
      let recrsData := rs.map (·.1)
      let recrsMeta <- storeMetadata ⟨<- rs.mapM (.link <$> storeMetadata ·.2)⟩
      let as <- storeMetadata ⟨<- all.mapM (.name <$> dematerializeName ·)⟩
      let data := ⟨recr, refl, usafe, lvls.length, params, indices, nested, t.data, ctorsData, recrsData⟩
      let meta := ⟨[.name n, .link ls, .link t.meta, .link as, .link ctorsMeta, .link recrsMeta]⟩
      pure (data, meta)
    go : Ix.Const -> CompileM (Ixon × Ixon)
    | .axiom ⟨name, lvls, type, isUnsafe⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let data := .axio ⟨isUnsafe, lvls.length, t.data⟩
      let meta := .meta ⟨[.name n, .link ls]⟩
      pure (data, meta)
    | .quotient ⟨name, lvls, type, kind⟩ => do
      let n <- dematerializeName name
      let ls <- storeMetadata ⟨<- lvls.mapM (.name <$> dematerializeName ·)⟩
      let t <- dematerializeExpr type
      let data := .quot ⟨kind, lvls.length, t.data⟩
      let meta := .meta ⟨[.name n, .link ls, .link t.meta]⟩
      pure (data, meta)
    | .definition d => (fun (d, m) => (.defn d, .meta m)) <$> goDef d
    | .inductiveProj ⟨name, block, idx⟩ => do
      let n <- dematerializeName name
      let data := .iprj ⟨idx, block.data⟩
      let meta := .meta ⟨[.name n, .link block.meta]⟩
      pure (data, meta)
    | .constructorProj ⟨name, block, idx, induct, cidx⟩ => do
      let n <- dematerializeName name
      let ind <- dematerializeName induct
      let data := .cprj ⟨idx, cidx, block.data⟩
      let meta := .meta ⟨[.name n, .link block.meta, .name ind]⟩
      pure (data, meta)
    | .recursorProj ⟨name, block, idx, induct, ridx⟩ => do
      let n <- dematerializeName name
      let ind <- dematerializeName induct
      let data := .rprj ⟨idx, ridx, block.data⟩
      let meta := .meta ⟨[.name n, .link block.meta, .name ind]⟩
      pure (data, meta)
    | .definitionProj ⟨name, block, idx⟩ => do
      let n <- dematerializeName name
      let data := .dprj ⟨idx, block.data⟩
      let meta := .meta ⟨[.name n, .link block.meta]⟩
      pure (data, meta)
    | .mutual block => do
      let mut data := #[]
      let mut meta := #[]
      -- iterate through each equivalence class
      for defsClass in block.defs do
        let mut classData := #[]
        let mut classMeta := #[]
        -- dematerialize each def in a class
        for defn in defsClass do
          let (defn', meta') <- goDef defn
          classData := classData.push defn'
          -- build up the class metadata as a list of links to the def metadata
          classMeta := classMeta.push (.link (<- storeMetadata meta'))
        -- make sure we have no empty classes and all defs in a class are equal
        match classData.toList with
          | [] => throw (.dematBadMutualBlock block)
          | [x] => data := data.push x
          | x::xs =>
            if xs.foldr (fun y acc => (y == x) && acc) true
            then data := data.push x
            else throw (.dematBadMutualBlock block)
        -- build up the block metadata as a list of links to the class metadata
        meta := meta.push (.link (<- storeMetadata ⟨classMeta.toList⟩))
      pure (.defs data.toList, .meta ⟨meta.toList⟩)
    | .inductive block => do
      let mut data := #[]
      let mut meta := #[]
      -- iterate through each equivalence class
      for indsClass in block.inds do
        let mut classData := #[]
        let mut classMeta := #[]
        -- dematerialize each inductive in a class
        for indc in indsClass do
          let (indc', meta') <- goInd indc
          classData := classData.push indc'
          -- build up the class metadata as a list of links to the indc metadata
          classMeta := classMeta.push (.link (<- storeMetadata meta'))
        -- make sure we have no empty classes and all defs in a class are equal
        match classData.toList with
          | [] => throw (.dematBadInductiveBlock block)
          | [x] => data := data.push x
          | x::xs =>
            if xs.foldr (fun y acc => (y == x) && acc) true
            then data := data.push x
            else throw (.dematBadInductiveBlock block)
        -- build up the block metadata as a list of links to the class metadata
        meta := meta.push (.link (<- storeMetadata ⟨classMeta.toList⟩))
      pure (.inds data.toList, .meta ⟨meta.toList⟩)

def dematerializeSubstring : Substring -> CompileM Ixon.Substring
| ⟨str, startPos, stopPos⟩ => do
    pure ⟨<- storeString str, startPos.byteIdx, stopPos.byteIdx⟩

def dematerializeSourceInfo : Lean.SourceInfo -> CompileM Ixon.SourceInfo
| .original l p t e => do
  let l' <- dematerializeSubstring l
  let t' <- dematerializeSubstring t
  pure <| .original l' p.byteIdx t' e.byteIdx
| .synthetic p e c => pure (.synthetic p.byteIdx e.byteIdx c)
| .none => pure .none

def dematerializePreresolved : Lean.Syntax.Preresolved -> CompileM Ixon.Preresolved
| .namespace ns => .namespace <$> dematerializeName ns
| .decl n fs => .decl <$> dematerializeName n <*> fs.mapM storeString

partial def dematerializeSyntax (syn: Lean.Syntax) : CompileM Ixon.Syntax := do
  dbg_trace "dematerializeSyntax {(<- read).current}"
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
      let info' <- dematerializeSourceInfo info
      let kind' <- dematerializeName kind
      let args' <- args.toList.mapM (dematerializeSyntax · >>= storeSerial)
      pure <| .node info' kind' args'
    | .atom info val => do
      let info' <- dematerializeSourceInfo info 
      let val' <- storeString val
      pure <| .atom info' val'
    | .ident info rawVal val preresolved => do
      let info' <- dematerializeSourceInfo info
      let rawVal' <- dematerializeSubstring rawVal
      let val' <- dematerializeName val
      let ps' <- preresolved.mapM dematerializePreresolved
      pure <| .ident info' rawVal' val' ps'

def dematerializeDataValue : Lean.DataValue -> CompileM Ixon.DataValue
| .ofString s => .ofString <$> storeString s
| .ofBool b => pure (.ofBool b)
| .ofName n => .ofName <$> dematerializeName n
| .ofNat i => .ofName <$> storeNat i
| .ofInt i => .ofInt <$> storeSerial i
| .ofSyntax s => .ofSyntax <$> (dematerializeSyntax s >>= storeSerial)

def dematerializeKVMaps (maps: List Lean.KVMap): CompileM Address := do
  storeIxon (.meta ⟨<- maps.mapM go⟩)
  where
    go (map: Lean.KVMap): CompileM Metadatum := do
    let mut list := #[]
    for (name, dataValue) in map do
      let n <- dematerializeName name
      let d <- dematerializeDataValue dataValue
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

partial def compileExpr (kvs: List Lean.KVMap) (expr: Lean.Expr): CompileM Ix.Expr := do
  match (<- get).exprCache.find? expr with
  | some x => pure x
  | none => do
    --dbg_trace "compileExpr go {(<- get).exprCache.size} {(<- read).current}"
    let expr' <- go expr
    --let _ <- dematerializeExpr expr'
    --dbg_trace "compileExpr exprCache {(<- get).exprCache.size} {(<- read).current}"
    modifyGet fun stt => (expr', { stt with
      exprCache := stt.exprCache.insert expr expr'
    })
  where
    kv := dematerializeKVMaps kvs
    go : Lean.Expr -> CompileM Ix.Expr
    | (.mdata kv x) => do
      --dbg_trace "compileExpr mdata {(<- read).current}"
      compileExpr (kv::kvs) x
    | .bvar idx => do 
      --dbg_trace "compileExpr bvar {(<- read).current}"
      match (← read).bindCtx[idx]? with
      -- Bound variables must be in the bind context
      | some _ => return .var (<- kv) idx
      | none => throw $ .invalidBVarIndex idx
    | .sort lvl => .sort <$> kv <*> compileLevel lvl
    | .const name lvls => do
      --dbg_trace "compileExpr const {name} {(<- read).current}"
      let univs ← lvls.mapM compileLevel
      match (← read).mutCtx.find? name with
      | some i => return .rec_ (<- kv) name i univs
      | none => match (<- get).comms.find? name with
        | some addr => return .const (<- kv) name addr univs
        | none => do
          let addr <- findLeanConst name >>= compileConst >>= dematerializeConst
          return .const (<- kv) name addr univs
    | .app fnc arg => do
      --dbg_trace "compileExpr app {(<- read).current}"
      .app <$> kv <*> compileExpr [] fnc <*> compileExpr [] arg
    | .lam name typ bod info => do
      --dbg_trace "compileExpr lam {(<- read).current}"
      let t <- compileExpr [] typ
      let b <- withBinder name <| compileExpr [] bod
      return .lam (<- kv) name info t b
    | .forallE name dom img info => do
      --dbg_trace "compileExpr all {(<- read).current}"
      let d <- compileExpr [] dom
      let i <- withBinder name <| compileExpr [] img
      return .pi (<- kv) name info d i
    | .letE name typ val bod nD => do
      --dbg_trace "compileExpr let {(<- read).current}"
      let t <- compileExpr [] typ
      let v <- compileExpr [] val
      let b <- withBinder name <| compileExpr [] bod
      return .letE (<- kv) name t v b nD
    | .lit lit => return .lit (<- kv) lit
    | .proj name idx exp => do
      --dbg_trace "compileExpr proj {(<- read).current}"
      let addr <- findLeanConst name >>= compileConst >>= dematerializeConst
      return .proj (<- kv) name addr idx (<- compileExpr [] exp)
    | expr@(.fvar ..)  => throw $ .exprFreeVariable expr
    | expr@(.mvar ..)  => throw $ .exprMetavariable expr

partial def compileConst (const : Lean.ConstantInfo) : CompileM Ix.Const := do
  match (<- get).constCache.find? const with
  | some x => pure x
  | none => resetCtx const.name <| do
    let const' <- go const
    let addr <- dematerializeConst const'
    let stt <- get
    dbg_trace "✓ compileConst {const.name}"
    dbg_trace "store {stt.store.size}"
    dbg_trace "constNames {stt.constNames.size}"
    dbg_trace "constCache {stt.constCache.size}"
    dbg_trace "exprCache {stt.exprCache.size}"
    dbg_trace "nameCache {stt.nameCache.size}"
    dbg_trace "synCache {stt.synCache.size}"
    dbg_trace "strCache {stt.strCache.size}"
    dbg_trace "univCache {stt.univCache.size}"
    modifyGet fun stt => (const', { stt with
      constNames := stt.constNames.insert const.name addr
      constCache := stt.constCache.insert const const'
    })
  where
    go : Lean.ConstantInfo -> CompileM Ix.Const
    | .defnInfo val => compileDefinition (mkPreDef val)
    | .thmInfo val => compileDefinition (mkPreTheorem val)
    | .opaqueInfo val => compileDefinition (mkPreOpaque val)
    | .inductInfo val => compileInductive val
    -- compile constructors through their parent inductive
    | .ctorInfo val => do match <- findLeanConst val.induct with
      | .inductInfo ind => do
        let _ <- compileInductive ind
        compileConst (.ctorInfo val)
      | c => throw $ .invalidConstantKind c.name "inductive" c.ctorName
    -- compile recursors through their parent inductive
    | .recInfo val => do
      match ← findLeanConst val.getMajorInduct with
      | .inductInfo ind => do
        let _ <- compileInductive ind
        compileConst (.recInfo val)
      | c => throw $ .invalidConstantKind c.name "inductive" c.ctorName
    | .axiomInfo ⟨⟨name, lvls, type⟩, isUnsafe⟩ => withLevels lvls do
      return .axiom ⟨name, lvls, <- compileExpr [] type, isUnsafe⟩
    | .quotInfo ⟨⟨name, lvls, type⟩, kind⟩ => withLevels lvls do
      return .quotient ⟨name, lvls, <- compileExpr [] type, kind⟩

partial def preDefToIR (d: PreDef) : CompileM Ix.Definition :=
  withLevels d.levelParams do
    let typ <- compileExpr [] d.type
    let val <- compileExpr [] d.value
    return ⟨d.name, d.levelParams, typ, d.kind, val, d.hints, d.safety, d.all⟩

partial def compileDefinition: PreDef -> CompileM Ix.Const
| defn => do
  -- single definition outside a mutual block
  if defn.all matches [_] then
    return .definition (<- withMutCtx (.single defn.name 0) <| preDefToIR defn)
  else do
  -- collecting and sorting all definitions in the mutual block
  let mut defs : Array PreDef := #[]
  for name in defn.all do
    match <- findLeanConst name with
    | .defnInfo x => defs := defs.push (mkPreDef x)
    | .opaqueInfo x => defs := defs.push (mkPreOpaque x)
    | .thmInfo x => defs := defs.push (mkPreTheorem x)
    | x => throw $ .invalidConstantKind x.name "mutdef" x.ctorName
  let mutDefs <- sortDefs defs.toList
  let mutCtx := defMutCtx mutDefs
  let definitions ← withMutCtx mutCtx <| mutDefs.mapM (·.mapM preDefToIR)
  -- add top-level mutual block to our state
  let block ← dematerializeConst <| .mutual ⟨definitions⟩
  modify fun stt => { stt with blocks := stt.blocks.insert block }
  -- then add all the projections, returning the def we started with
  let mut ret? : Option Ix.Const := none
  for name in defn.all do
    let idx <- do match mutCtx.find? name with
    | some idx => pure idx
    | none => throw $ .cantFindMutDefIndex name
    let const <- findLeanConst name
    let const' := .definitionProj ⟨name, block, idx⟩
    let addr <- dematerializeConst const'
    modify fun stt => { stt with
      constNames := stt.constNames.insert name addr
      constCache := stt.constCache.insert const const'
    }
    if name == defn.name then ret? := some const'
  match ret? with
  | some ret => return ret
  | none => throw $ .compileMutualBlockMissingProjection defn.name

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

/-- AST comparison of two Lean definitions. --/
partial def compareDef (ctx: MutCtx) (x y: PreDef)
  : CompileM Ordering := do
  dbg_trace "compareDefs constCmp {(<- get).constCmp.size} {(<- read).current}"
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

/--
`sortDefs` recursively sorts a list of mutual definitions into equivalence classes.
At each stage, we take as input the current best known equivalence
classes (held in the `mutCtx` of the CompileEnv). For most cases, equivalence
can be determined by syntactic differences which are invariant to the current
best known classification. For example:

```
mutual
  def : Nat := 1
  def bar : Nat := 2
end
```

are both different due to the different values in the definition. We call this a
"strong" ordering, and comparisons between defintions that produce strong
orderings are cached across compilation.

However, there are also weak orderings, where the order of definitions in a
mutual block depends on itself.

```
mutual
  def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + 1

  def B : Nat → Nat
  | 0 => 0
  | n + 1 => C n + 1

  def C : Nat → Nat
  | 0 => 0
  | n + 1 => A n + 1
end
```

Here since any reference to A, B, C has to be compiled into an index, the
ordering chosen for A, B, C will effect itself, since we compile into
something that looks, with order [A, B, C] like:

```
mutual
  def #1 : Nat → Nat
  | 0 => 0
  | n + 1 => #2 n + #3 n + 1

  def #2 : Nat → Nat
  | 0 => 0
  | n + 1 => #3 n + 1

  def #3 : Nat → Nat
  | 0 => 0
  | n + 1 => #1 n + 1
end
```

This is all well and good, but if we chose order `[C, B, A]` then the block
would compile as

```
mutual
  def #1 : Nat → Nat
  | 0 => 0
  | n + 1 => #3 n + 1

  def #2 : Nat → Nat
  | 0 => 0
  | n + 1 => #1 n + 1

  def #3 : Nat → Nat
  | 0 => 0
  | n + 1 => #2 n + #1 n + 1
end
```

with completely different hashes. So we need to figure out a canonical order for
such mutual blocks.

We start by assuming that all definitions in a mutual block are equal and then
recursively refining this assumption through successive sorting passes, similar
to partition refinement:
```
classes₀ := [startDefs]
classes₁ := sortDefs classes₀
classes₂ := sortDefs classes₁
classes₍ᵢ₊₁₎ := sortDefs classesᵢ ...
```
Initially, `startDefs` is simply the list of definitions we receive from
`DefinitionVal.all`, sorted by name. We assume that at we will reach some
fixed-point where `classes₍ᵢ₊₁₎ := classesᵢ` and no further refinement is
possible (we have not rigourously proven such a fixed point exists, but
it seams reasonable given that after the first pass to find the strongly ordered
definitions, the algorithm should only separate partitions into smaller ones)
-/
partial def sortDefs (classes : List PreDef) : CompileM (List (List PreDef)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List PreDef)): CompileM (List (List PreDef)) := do
      dbg_trace "sortDefs blocks {(<- get).blocks.size} {(<- read).current}"
      let ctx := defMutCtx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .emptyDefsClass cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareDef ctx) >>= List.groupByM (eqDef ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'

partial def makePreInd (ind: Lean.InductiveVal) : CompileM Ix.PreInd := do
  let ctors <- ind.ctors.mapM getCtor
  let recrs := (<- get).env.constants.fold getRecrs []
  return ⟨ind.name, ind.levelParams, ind.type, ind.numParams, ind.numIndices,
    ind.all, ctors, recrs, ind.numNested, ind.isRec, ind.isReflexive, ind.isUnsafe⟩
  where
    getCtor (name: Lean.Name) : CompileM (Lean.ConstructorVal) := do
      match (<- findLeanConst name) with
      | .ctorInfo c => pure c
      | _ => throw <| .invalidConstantKind name "constructor" ""
    getRecrs (acc: List Lean.RecursorVal) : Lean.Name -> Lean.ConstantInfo -> List Lean.RecursorVal
    | .str n .., .recInfo r
    | .num n .., .recInfo r => if n == ind.name then r::acc else acc
    | _, _ => acc

/--
Content-addresses an inductive and all inductives in the mutual block as a
mutual block, even if the inductive itself is not in a mutual block.

Content-addressing an inductive involves content-addressing its associated
constructors and recursors, hence the complexity of this function.
-/
partial def compileInductive: Lean.InductiveVal -> CompileM Ix.Const
| ind => do
  let mut preInds := #[]
  let mut ctorNames : RBMap Lean.Name (List Lean.Name × List Lean.Name) compare := {}
  -- collect all mutual inductives as Ix.PreInds
  for n in ind.all do
    match <- findLeanConst n with
    | .inductInfo ind =>
      let preInd <- makePreInd ind
      preInds := preInds.push preInd
      ctorNames := ctorNames.insert n (ind.ctors, preInd.recrs.map (·.name))
    | c => throw <| .invalidConstantKind c.name "inductive" c.ctorName
  -- sort PreInds into equivalence classes
  let mutInds <- sortInds preInds.toList
  let mutCtx := indMutCtx mutInds
  -- compile each preinductive with the mutCtx
  let inds ← withMutCtx mutCtx <| mutInds.mapM (·.mapM preInductiveToIR)
  -- add top-level mutual block to our state
  let block <- dematerializeConst <| .inductive ⟨inds⟩
  modify fun stt => { stt with blocks := stt.blocks.insert block }
  -- then add all projections, returning the inductive we started with
  let mut ret? : Option Ix.Const := none
  for (name, idx) in ind.all.zipIdx do
    let const <- findLeanConst name
    let const' := .inductiveProj ⟨name, block, idx⟩
    let addr <- dematerializeConst const'
    modify fun stt => { stt with
      constNames := stt.constNames.insert name addr
      constCache := stt.constCache.insert const const'
    }
    if name == ind.name then ret? := some const'
    let some (ctors, recrs) := ctorNames.find? ind.name
      | throw $ .cantFindMutDefIndex ind.name
    for (cname, cidx) in ctors.zipIdx do
      -- Store and cache constructor projections
      let cconst <- findLeanConst cname
      let cconst' := .constructorProj ⟨cname, block, idx, name, cidx⟩
      let caddr <- dematerializeConst cconst'
      modify fun stt => { stt with
        constNames := stt.constNames.insert cname caddr
        constCache := stt.constCache.insert cconst cconst'
      }
    for (rname, ridx) in recrs.zipIdx do
      -- Store and cache recursor projections
      let rconst <- findLeanConst rname
      let rconst' := .recursorProj ⟨rname, block, idx, name, ridx⟩
      let raddr <- dematerializeConst rconst'
      modify fun stt => { stt with
        constNames := stt.constNames.insert rname raddr
        constCache := stt.constCache.insert rconst rconst'
      }
  match ret? with
  | some ret => return ret
  | none => throw $ .compileInductiveBlockMissingProjection ind.name

partial def preInductiveToIR (ind : Ix.PreInd) : CompileM Ix.Inductive 
  := withLevels ind.levelParams $ do
  let (recs, ctors) := <- ind.recrs.foldrM (init := ([], [])) collectRecsCtors
  let type <- compileExpr [] ind.type
    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
    -- match the order used in `mutCtx`
  return ⟨ind.name, ind.levelParams, type, ind.numParams, ind.numIndices,
    ind.all, ctors, recs, ind.numNested, ind.isRec, ind.isReflexive, ind.isUnsafe⟩
  where
    collectRecsCtors : Lean.RecursorVal -> List Recursor × List Constructor
    -> CompileM (List Recursor × List Constructor)
    | r, (recs, ctors) =>
      if isInternalRec r.type ind.name then do
        let (thisRec, thisCtors) <- internalRecToIR (ind.ctors.map (·.name)) r
        pure (thisRec :: recs, thisCtors)
      else do
        let thisRec ← externalRecToIR r
        pure (thisRec :: recs, ctors)

partial def internalRecToIR (ctors : List Lean.Name) (recr: Lean.RecursorVal)
  : CompileM (Ix.Recursor × List Ix.Constructor) 
  := withLevels recr.levelParams do
    let typ ← compileExpr [] recr.type
    let (retCtors, retRules) ← recr.rules.foldrM (init := ([], []))
      fun r (retCtors, retRules) => do
        if ctors.contains r.ctor then
          let (ctor, rule) ← recRuleToIR r
          pure $ (ctor :: retCtors, rule :: retRules)
        else pure (retCtors, retRules) -- this is an external recursor rule
    let recr := ⟨recr.name, recr.levelParams, typ, recr.numParams, recr.numIndices,
      recr.numMotives, recr.numMinors, retRules, recr.k, recr.isUnsafe⟩
    return (recr, retCtors)

partial def externalRecToIR: Lean.RecursorVal -> CompileM Recursor
| recr => withLevels recr.levelParams do
    let typ ← compileExpr [] recr.type
    let rules ← recr.rules.mapM externalRecRuleToIR
    return ⟨recr.name, recr.levelParams, typ, recr.numParams, recr.numIndices,
      recr.numMotives, recr.numMinors, rules, recr.k, recr.isUnsafe⟩

partial def recRuleToIR: Lean.RecursorRule -> CompileM (Ix.Constructor × Ix.RecursorRule)
| rule => do
  let rhs ← compileExpr [] rule.rhs
  match ← findLeanConst rule.ctor with
  | .ctorInfo ctor => withLevels ctor.levelParams do
    let typ ← compileExpr [] ctor.type
    let ctor := ⟨ctor.name, ctor.levelParams, typ, ctor.cidx,
      ctor.numParams, ctor.numFields, ctor.isUnsafe⟩
    pure (ctor, ⟨rule.ctor, rule.nfields, rhs⟩)
  | const =>
    throw $ .invalidConstantKind const.name "constructor" const.ctorName

partial def externalRecRuleToIR: Lean.RecursorRule -> CompileM RecursorRule
| rule => do return ⟨rule.ctor, rule.nfields, <- compileExpr [] rule.rhs⟩

/-- AST comparison of two Lean inductives. --/
partial def compareInd (ctx: MutCtx) (x y: PreInd) 
  : CompileM Ordering := do
  dbg_trace "compareInd constCmp {(<- get).constCmp.size} {(<- read).current}"
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
      SOrder.cmpM (pure ⟨true, compare x.recrs.length y.recrs.length⟩) <|
      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
      SOrder.cmpM (SOrder.zipM compareCtor x.ctors y.ctors)
        (SOrder.zipM compareRecr x.recrs y.recrs)
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
    compareRecr (x y: Lean.RecursorVal) : CompileM SOrder := do
      let key := match compare x.name y.name with
        | .lt => (x.name, y.name)
        | _ => (y.name, x.name)
      match (<- get).constCmp.find? key with
      | some o => return ⟨true, o⟩
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
      return sorder
    compareRule (xlvls ylvls: List Lean.Name) (x y: Lean.RecursorRule)
      : CompileM SOrder := do
        SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩)
          (compareExpr ctx xlvls ylvls x.rhs y.rhs)

partial def eqInd (ctx: MutCtx) (x y: PreInd) : CompileM Bool :=
  (fun o => o == .eq) <$> compareInd ctx x y

/-- `sortInds` recursively sorts a list of inductive datatypes into equivalence
classes, analogous to `sortDefs` --/
partial def sortInds (classes : List PreInd) : CompileM (List (List PreInd)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
  where
    go (cs: List (List PreInd)): CompileM (List (List PreInd)) := do
      dbg_trace "sortInds blocks {(<- get).blocks.size} {(<- read).current}"
      let ctx := indMutCtx cs
      let cs' <- cs.mapM fun ds =>
        match ds with
        | []  => throw <| .emptyIndsClass cs
        | [d] => pure [[d]]
        | ds  => ds.sortByM (compareInd ctx) >>= List.groupByM (eqInd ctx)
      let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
      if cs == cs' then return cs' else go cs'
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
  let typ' <- compileExpr [] typ
  let val' <- compileExpr [] val
  let anon := .definition ⟨.anonymous, lvls, typ', .definition, val', .opaque, .safe, []⟩
  let anonAddr <- dematerializeConst anon
  let name := anonAddr.data.toUniqueName
  let const := .definition ⟨name, lvls, typ', .definition, val', .opaque, .safe, []⟩
  let addr <- dematerializeConst const
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
