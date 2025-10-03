import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.IR
import Ix.Common
--import Ix.Store
import Ix.SOrder
import Ix.Cronos

open Std (HashMap)
--open Ix.TransportM

namespace Ix
open Ixon

structure CompileEnv where
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  mutCtx  : MutCtx
deriving BEq, Hashable

def CompileEnv.init: CompileEnv := ⟨default, default, default⟩

structure CompileState where
  maxHeartBeats: USize
  env: Lean.Environment
  prng: StdGen
  store: HashMap Address ByteArray
  names: HashMap Lean.Name Address
  univCache: HashMap Lean.Level Ix.Level
  univAddrs: HashMap Ix.Level MetaAddress
  constCache: HashMap Lean.ConstantInfo Ix.Const
  constAddrs : HashMap Ix.Const MetaAddress
  exprCache: HashMap Lean.Expr Ix.Expr
  exprAddrs: HashMap Ix.Expr MetaAddress
  comms: HashMap Lean.Name MetaAddress
  constCmp: HashMap (Lean.Name × Lean.Name) Ordering
  exprCmp: HashMap (CompileEnv × Lean.Expr × Lean.Expr) Ordering
  axioms: Std.HashMap Lean.Name MetaAddress
  blocks: Std.HashSet MetaAddress
  cronos: Cronos

def CompileState.init (env: Lean.Environment) (seed: Nat) (maxHeartBeats: USize) : CompileState :=
  ⟨maxHeartBeats, env, mkStdGen seed, default, default, default, default,
  default, default, default, default, default, default, default, default,
  default, default⟩

inductive CompileError where
| unknownConstant : Lean.Name → CompileError
| unfilledLevelMetavariable : Lean.Level → CompileError
--| unfilledExprMetavariable : Lean.Expr → CompileError
--| invalidBVarIndex : Nat → CompileError
--| freeVariableExpr : Lean.Expr → CompileError
--| metaVariableExpr : Lean.Expr → CompileError
--| metaDataExpr : Lean.Expr → CompileError
| levelNotFound : Lean.Name → List Lean.Name -> String → CompileError
--| invalidConstantKind : Lean.Name → String → String → CompileError
--| constantNotContentAddressed : Lean.Name → CompileError
--| nonRecursorExtractedFromChildren : Lean.Name → CompileError
--| cantFindMutDefIndex : Lean.Name → CompileError
----| transportError : TransportError → CompileError
--| kernelException : Lean.Kernel.Exception → CompileError
--| cantPackLevel : Nat → CompileError
--| nonCongruentInductives : PreInductive -> PreInductive -> CompileError
--| alphaInvarianceFailure : Ix.Const -> Address -> Ix.Const -> Address -> CompileError
--| emptyDefsEquivalenceClass: List (List PreDefinition) -> CompileError
--| emptyIndsEquivalenceClass: List (List PreInductive) -> CompileError
--
--def CompileError.pretty : CompileError -> IO String
--| .unknownConstant n => pure s!"Unknown constant '{n}'"
--| .unfilledLevelMetavariable l => pure s!"Unfilled level metavariable on universe '{l}'"
--| .unfilledExprMetavariable e => pure s!"Unfilled level metavariable on expression '{e}'"
--| .invalidBVarIndex idx => pure s!"Invalid index {idx} for bound variable context"
--| .freeVariableExpr e => pure s!"Free variable in expression '{e}'"
--| .metaVariableExpr e => pure s!"Metavariable in expression '{e}'"
--| .metaDataExpr e => pure s!"Meta data in expression '{e}'"
--| .levelNotFound n ns msg => pure s!"'Level {n}' not found in '{ns}', {msg}"
--| .invalidConstantKind n ex gt => pure s!"Invalid constant kind for '{n}'. Expected '{ex}' but got '{gt}'"
--| .constantNotContentAddressed n => pure s!"Constant '{n}' wasn't content-addressed"
--| .nonRecursorExtractedFromChildren n => pure
--  s!"Non-recursor '{n}' extracted from children"
--| .cantFindMutDefIndex n => pure s!"Can't find index for mutual definition '{n}'"
----| .transportError n => pure s!"compiler transport error '{repr n}'"
--| .kernelException e => (·.pretty 80) <$> (e.toMessageData .empty).format
--| .cantPackLevel n => pure s!"Can't pack level {n} greater than 2^256'"
--| .nonCongruentInductives a b => pure s!"noncongruent inductives {a.name} {b.name}'"
--| .alphaInvarianceFailure x xa y ya => 
--  pure s!"alpha invariance failure {repr x} hashes to {xa}, but {repr y} hashes to {ya}"
--| .emptyDefsEquivalenceClass dss => 
--  pure s!"empty equivalence class while sorting definitions {dss.map fun ds => ds.map (·.name)}"
--| .emptyIndsEquivalenceClass dss => 
--  pure s!"empty equivalence class while sorting inductives {dss.map fun ds => ds.map (·.name)}"

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
--def withCurrent (name: Lean.Name) : CompileM α -> CompileM α :=
--  withReader $ fun c => { c with current := name }

-- add binding name to local context
def withBinder (name: Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def withLevels (lvls : List Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def withMutCtx (mutCtx : Std.HashMap Lean.Name Nat)
  : CompileM α -> CompileM α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

-- reset local context
def resetCtx : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := [], bindCtx := [], mutCtx := {} }

def resetCtxWithLevels (lvls: List Lean.Name) : CompileM α -> CompileM α :=
  withReader $ fun c => { c with univCtx := lvls, bindCtx := [], mutCtx := {} }

def storeIxon (ixon: Ixon): CompileM Address := do
  let bytes := Ixon.ser ixon
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def storeString (str: String): CompileM Address := do
  let bytes := str.toUTF8
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def storeNat (nat: Nat): CompileM Address := do
  let bytes := nat.toBytesLE
  let addr := Address.blake3 ⟨bytes⟩
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr ⟨bytes⟩
  })

def storeMetadata (meta: Metadata): CompileM Address := do
  let bytes := Ixon.ser meta
  let addr := Address.blake3 bytes
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr bytes
  })

def dematerializeName (name: Lean.Name): CompileM Address := do
  match (<- get).names.get? name with
  | some addr => pure addr
  | none => do
    let addr <- go name
    modifyGet fun stt => (addr, { stt with
      names := stt.names.insert name addr
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
  | x@(.mvar ..), _ => throw $ .unfilledLevelMetavariable x
  | _, y@(.mvar ..) => throw $ .unfilledLevelMetavariable y
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
  match (<- get).univAddrs.get? lvl with
  | some l => pure l
  | none => do
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
  match (<- get).univCache.get? lvl with
  | some l => pure l
  | none => do
    let lvl' <- go lvl
    let _ <- dematerializeLevel lvl'
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
    | l@(.mvar ..) => throw $ .unfilledLevelMetavariable l

def dematerializeExpr (expr: Ix.Expr): CompileM MetaAddress := do
  match (<- get).exprAddrs.get? expr with
  | some x => pure x
  | none => do
    let (anon, meta) <- go expr
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    modifyGet fun stt => (maddr, { stt with
      exprAddrs := stt.exprAddrs.insert expr maddr
    })
  where
    go : Ix.Expr -> CompileM (Ixon × Ixon)
    | .var kvs idx => pure (.evar idx, .meta ⟨kvs.map .kvmap⟩)
    | .sort kvs univ => do
      let ⟨udata, umeta⟩ <- dematerializeLevel univ
      let data := .esort udata
      let meta := .meta { nodes := [.link umeta] ++ kvs.map .kvmap}
      pure (data, meta)
    | .const kvs name ref univs => do
      let n <- dematerializeName name
      let us <- univs.mapM dematerializeLevel
      let data := .eref ref.data (us.map (·.data))
      let meta := .meta ⟨[.name n, .link ref.meta] ++ us.map (.name ·.meta) ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .rec_ kvs name idx univs => do
      let n <- dematerializeName name
      let us <- univs.mapM dematerializeLevel
      let data := .erec idx (us.map (·.data))
      let meta := .meta ⟨[.name n] ++ us.map (.name ·.meta) ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .app kvs func argm => do
      let f' <- dematerializeExpr func
      let a' <- dematerializeExpr argm
      let data := .eapp f'.data a'.data
      let meta := .meta ⟨[.link f'.meta, .link a'.meta] ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .lam kvs name info type body => do
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let b' <- dematerializeExpr body
      let data := .elam t'.data b'.data
      let meta := .meta ⟨[.name n, .info info, .link t'.meta, .link b'.meta] ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .pi kvs name info type body => do
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let b' <- dematerializeExpr body
      let data := .eall t'.data b'.data
      let meta := .meta ⟨[.name n, .info info, .link t'.meta, .link b'.meta] ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .letE kvs name type value body nD => do
      let n <- dematerializeName name
      let t' <- dematerializeExpr type
      let v' <- dematerializeExpr value
      let b' <- dematerializeExpr body
      let data := .elet nD t'.data v'.data b'.data
      let meta := .meta ⟨[.name n, .link t'.meta, .link v'.meta, .link b'.meta] ++ kvs.map .kvmap⟩
      pure (data, meta)
    | .lit kvs (.natVal n) => do pure (.enat (<- storeNat n), .meta ⟨kvs.map .kvmap⟩)
    | .lit kvs (.strVal s) => do pure (.enat (<- storeString s), .meta ⟨kvs.map .kvmap⟩)
    | .proj kvs typeName type idx struct => do
      let n <- dematerializeName typeName
      let s' <- dematerializeExpr struct
      let data := .eprj type.data idx s'.data
      let meta := .meta ⟨[.name n, .link type.meta, .link s'.meta] ++ kvs.map .kvmap⟩
      pure (data, meta)

def dematerializeConst (const: Ix.Const): CompileM MetaAddress := do
  match (<- get).constAddrs.get? const with
  | some x => pure x
  | none => do
    let (anon, meta) <- go const
    let anonAddr <- storeIxon anon
    let metaAddr <- storeIxon meta
    let maddr := ⟨anonAddr, metaAddr⟩
    modifyGet fun stt => (maddr, { stt with
      constAddrs := stt.constAddrs.insert const maddr
    })
  where
    goDef : Ix.Definition -> CompileM (Ixon.Definition × Ixon.Metadata)
    | ⟨name, lvls, type, kind, value, hints, safety, all⟩ => do
      let n <- dematerializeName name
      let ls <- lvls.mapM (fun n => .name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let v <- dematerializeExpr value
      let as <- all.mapM (fun n => .name <$> dematerializeName n)
      let data := ⟨kind, safety, lvls.length, t.data, v.data⟩
      let meta := ⟨[.name n] ++ ls ++ [.link t.meta, .link v.meta] ++ as⟩
      pure (data, meta)
    goCtor : Ix.Constructor -> CompileM (Ixon.Constructor × Ixon.Metadata)
    | ⟨name, lvls, type, cidx, params, fields, usafe⟩ => do
      let n <- dematerializeName name
      let ls <- lvls.mapM (fun n => .name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let ctor := ⟨usafe, lvls.length, cidx, params, fields, t.data⟩
      let meta := ⟨[.name n] ++ ls ++ [.link t.meta]⟩
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
      let ls <- lvls.mapM (fun n => .name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let rules <- rules.mapM goRecrRule
      let rulesData := rules.map (·.1)
      let rulesMeta <- rules.mapM (fun x => .link <$> storeMetadata x.2)
      let recr := ⟨k, usafe, lvls.length, params, indices, motives, minors, t.data, rulesData⟩
      let meta := ⟨[.name n] ++ ls ++ [.link t.meta] ++ rulesMeta⟩
      pure (recr, meta)
    goInd : Ix.Inductive -> CompileM (Ixon.Inductive × Ixon.Metadata)
    | ⟨name, lvls, type, params, indices, all, ctors, recrs, nested, recr, refl, usafe⟩ => do
      let n <- dematerializeName name
      let ls <- lvls.mapM (fun n => Metadatum.name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let cs <- ctors.mapM goCtor
      let ctorsData := cs.map (·.1)
      let ctorsMeta <- cs.mapM (fun x=> Metadatum.link <$> storeMetadata x.2)
      let rs <- recrs.mapM goRecr
      let recrsData := rs.map (·.1)
      let recrsMeta <- rs.mapM (fun x=> Metadatum.link <$> storeMetadata x.2)
      let as <- all.mapM (fun n => Metadatum.name <$> dematerializeName n)
      let data := ⟨recr, refl, usafe, lvls.length, params, indices, nested, t.data, ctorsData, recrsData⟩
      let meta := ⟨[.name n] ++ ls ++ [.link t.meta] ++ ctorsMeta ++ recrsMeta⟩
      pure (data, meta)
    go : Ix.Const -> CompileM (Ixon × Ixon)
    | .axiom ⟨name, lvls, type, isUnsafe⟩ => do
      let n <- dematerializeName name
      let ls <- lvls.mapM (fun n => Metadatum.name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let data := .axio ⟨isUnsafe, lvls.length, t.data⟩
      let meta := .meta ⟨[.name n] ++ ls⟩
      pure (data, meta)
    | .quotient ⟨name, lvls, type, kind⟩ => do
      let n <- dematerializeName name
      let ls <- lvls.mapM (fun n => Metadatum.name <$> dematerializeName n)
      let t <- dematerializeExpr type
      let data := .quot ⟨kind, lvls.length, t.data⟩
      let meta := .meta ⟨[.name n] ++ ls ++ [.link t.meta]⟩
      pure (data, meta)
    | .definition d => (fun (d, m) => (.defn d, .meta m)) <$> goDef d
    | .inductiveProj _ => sorry
    | .constructorProj _ => sorry
    | .recursorProj _ => sorry
    | .definitionProj _ => sorry
    | .mutual ds => sorry
    | .inductive _ => sorry


--mutual
--/--
--Content-addresses a Lean expressio
---/
--partial def compileExpr (expr: Lean.Expr): CompileM Ix.Expr := do
--  match (<- get).exprCache.get? expr with
--  | some x => pure x
--  | none => do
--    let expr' <- go expr
--    let _ <- dematerializeExpr expr'
--    modifyGet fun stt => (lvl', { stt with
--      exprCache := stt.exprCache.insert expr expr'
--    })
--  where
--    go : Lean.Expr -> CompileM Ix.Expr
--    | .bvar idx => do match (← read).bindCtx[idx]? with
--      -- Bound variables must be in the bind context
--      | some _ => return .var idx
--      | none => throw $ .invalidBVarIndex idx
--    | .sort lvl => return .sort $ ← compileLevel lvl
--    | .const name lvls => do
--      let univs ← lvls.mapM compileLevel
--      match (← read).mutCtx.get? name with
--      -- recursing!
--      | some i => return .rec_ name i univs
--      | none => match (<- get).comms.get? name with
--        | some (commAddr, metaAddr) => do
--          return .const name commAddr metaAddr univs
--        | none => do
--          let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
--          return .const name contAddr metaAddr univs
--    | .app fnc arg => return .app (← compileExpr fnc) (← compileExpr arg)
--    | .lam name typ bod info =>
--      return .lam name info (← compileExpr typ) (← withBinder name $ compileExpr bod)
--    | .forallE name dom img info =>
--      return .pi name info (← compileExpr dom) (← withBinder name $ compileExpr img)
--    | .letE name typ exp bod nD =>
--      return .letE name (← compileExpr typ) (← compileExpr exp)
--        (← withBinder name $ compileExpr bod) nD
--    | .lit lit => return .lit lit
--    | .proj name idx exp => do
--      let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
--      return .proj name contAddr metaAddr idx (← compileExpr exp)
--    | expr@(.fvar ..)  => throw $ .freeVariableExpr expr
--    | expr@(.mvar ..)  => throw $ .metaVariableExpr expr
--    -- TODO: cursed
--    | (.mdata _ x) => compileExpr x
--
--/-- compile Lean Constant --/
--partial def compileConst (const : Lean.ConstantInfo) : CompileM Ix.Const := do
--  -- first check if we've already compiled this const
--  match (← get).names.get? const.name with
--  -- if we have, returned the cached address
--  | some (anonAddr, metaAddr) => do
--    pure (anonAddr, metaAddr)
--  -- if not, pattern match on the const
--  | none => do
--    dbg_trace "-> compileConst {const.name}";
--    let cronTag := s!"compileConst {const.name}"
--    cron cronTag
--    let cronTag2 := s!"constSize {const.name}"
--    dbg_trace "-> constSize {const.name}";
--    cron cronTag2
--    let size := const.size
--    cron cronTag2
--    dbg_trace "✓ {(<- getCron cronTag2)} {size}";
--    let addrs <- compileInner const
--    cron cronTag
--    let timing <- getCron cronTag
--    dbg_trace "✓ {timing}";
--    return addrs
--  where
--    compileInner (const: Lean.ConstantInfo) := resetCtx $ withCurrent const.name $ match const with
--    -- convert possible mutual block elements to PreDefinitions
--    | .defnInfo val => do
--      compileDefinition (mkPreDefinition val)
--    | .thmInfo val => do
--      compileDefinition (mkPreTheorem val)
--    | .opaqueInfo val => do
--      compileDefinition (mkPreOpaque val)
--    -- compile possible mutual inductive block elements
--    | .inductInfo val => do
--      compileInductive val
--    -- compile constructors through their parent inductive
--    | .ctorInfo val => do
--      match ← findLeanConst val.induct with
--      | .inductInfo ind => do
--        let _ <- compileInductive ind
--        compileConst (.ctorInfo val)
--      | const =>
--        throw $ .invalidConstantKind const.name "inductive" const.ctorName
--    -- compile recursors through their parent inductive
--    | .recInfo val => do
--      match ← findLeanConst val.getMajorInduct with
--      | .inductInfo ind => do
--        let _ <- compileInductive ind
--        compileConst (.recInfo val)
--      | const =>
--        throw $ .invalidConstantKind const.name "inductive" const.ctorName
--    -- The rest adds the constants to the cache one by one
--    | .axiomInfo val => resetCtxWithLevels const.levelParams do
--      let c := .axiom ⟨val.name, val.levelParams, ← compileExpr val.type, val.isUnsafe⟩
--      let (anonAddr, metaAddr) ← hashConst c
--      modify fun stt => { stt with
--        axioms := stt.axioms.insert const.name (anonAddr, metaAddr)
--        names := stt.names.insert const.name (anonAddr, metaAddr)
--      }
--      return (anonAddr, metaAddr)
--    | .quotInfo val => resetCtxWithLevels const.levelParams do
--      let type <- compileExpr val.type
--      let c := .quotient ⟨val.name, val.levelParams, type, val.kind⟩
--      let (anonAddr, metaAddr) ← hashConst c
--      modify fun stt => { stt with
--        axioms := (stt.axioms.insert const.name (anonAddr, metaAddr))
--        names := stt.names.insert const.name (anonAddr, metaAddr)
--      }
--      return (anonAddr, metaAddr)
--
--end
--def dematerializeConst (x: Ix.Const) : CompileM (Ixon × Ixon) :=
--  match dematerialize x with
--  | .ok (ix, tstt) => do
--    for (addr, ixon) in tstt.store do
--      let _ <- liftM (Store.forceWriteConst addr ixon).toIO
--    return (ix, Ixon.meta ⟨tstt.meta.toList⟩)
--  | .error e => throw (.transportError e)
--
--def cron (tag: String) : CompileM Unit := do
--  let stt <- get
--  let c <- liftM <| Cronos.clock stt.cronos tag
--  modify fun stt => { stt with cronos := c }
--
--def getCron (tag: String) : CompileM String := do
--  return (<- get).cronos.tagSummary tag

--def hashConst (const: Ix.Const) : CompileM MetaAddress := do
--  match (<- get).constAddrs.get? const with
--  | some m => pure m
--  | none => do
--    let (anonIxon, metaIxon) <- dematerializeConst const
--    let anonAddr <- storeConst anonIxon
--    let metaAddr <- storeConst metaIxon
--    let timing <- getCron cronTag
--    modifyGet fun stt => (⟨anonAddr, metaAddr⟩, { stt with
--      cache := stt.cache.insert const (anonAddr, metaAddr)
--    })


-- lookup or compute the addresses of a constant
--def hashConst (const: Ix.Const) : CompileM MetaAddress := do
--  match (<- get).constAddrs.get? const with
--  | some (anonAddr, metaAddr) => pure (anonAddr, metaAddr)
--  | none => do
--    let cronTag := s!"hashConst {const.name}"
--    dbg_trace "-> hashConst {const.name}";
--    cron cronTag
--    let (anonIxon, metaIxon) <- dematerializeConst const
--    let anonAddr <- storeConst anonIxon
--    let metaAddr <- storeConst metaIxon
--    cron cronTag
--    let timing <- getCron cronTag
--    dbg_trace "✓ {timing}";
--    dbg_trace "names: {(<- get).names.size}";
--    dbg_trace "cache: {(<- get).cache.size}";
--    dbg_trace "eqConst: {(<- get).eqConst.size}";
--    dbg_trace "blocks: {(<- get).blocks.size}";
--    modifyGet fun stt => ((anonAddr, metaAddr), { stt with
--      cache := stt.cache.insert const (anonAddr, metaAddr)
--    })

end Ix

--mutual
--
--/-- compile Lean Constant --/
--partial def compileConst (const : Lean.ConstantInfo)
--  : CompileM (Address × Address) := do
--  -- first check if we've already compiled this const
--  match (← get).names.get? const.name with
--  -- if we have, returned the cached address
--  | some (anonAddr, metaAddr) => do
--    pure (anonAddr, metaAddr)
--  -- if not, pattern match on the const
--  | none => do
--    dbg_trace "-> compileConst {const.name}";
--    let cronTag := s!"compileConst {const.name}"
--    cron cronTag
--    let cronTag2 := s!"constSize {const.name}"
--    dbg_trace "-> constSize {const.name}";
--    cron cronTag2
--    let size := const.size
--    cron cronTag2
--    dbg_trace "✓ {(<- getCron cronTag2)} {size}";
--    let addrs <- compileInner const
--    cron cronTag
--    let timing <- getCron cronTag
--    dbg_trace "✓ {timing}";
--    return addrs
--  where
--    compileInner (const: Lean.ConstantInfo) := resetCtx $ withCurrent const.name $ match const with
--    -- convert possible mutual block elements to PreDefinitions
--    | .defnInfo val => do
--      compileDefinition (mkPreDefinition val)
--    | .thmInfo val => do
--      compileDefinition (mkPreTheorem val)
--    | .opaqueInfo val => do
--      compileDefinition (mkPreOpaque val)
--    -- compile possible mutual inductive block elements
--    | .inductInfo val => do
--      compileInductive val
--    -- compile constructors through their parent inductive
--    | .ctorInfo val => do
--      match ← findLeanConst val.induct with
--      | .inductInfo ind => do
--        let _ <- compileInductive ind
--        compileConst (.ctorInfo val)
--      | const =>
--        throw $ .invalidConstantKind const.name "inductive" const.ctorName
--    -- compile recursors through their parent inductive
--    | .recInfo val => do
--      match ← findLeanConst val.getMajorInduct with
--      | .inductInfo ind => do
--        let _ <- compileInductive ind
--        compileConst (.recInfo val)
--      | const =>
--        throw $ .invalidConstantKind const.name "inductive" const.ctorName
--    -- The rest adds the constants to the cache one by one
--    | .axiomInfo val => resetCtxWithLevels const.levelParams do
--      let c := .axiom ⟨val.name, val.levelParams, ← compileExpr val.type, val.isUnsafe⟩
--      let (anonAddr, metaAddr) ← hashConst c
--      modify fun stt => { stt with
--        axioms := stt.axioms.insert const.name (anonAddr, metaAddr)
--        names := stt.names.insert const.name (anonAddr, metaAddr)
--      }
--      return (anonAddr, metaAddr)
--    | .quotInfo val => resetCtxWithLevels const.levelParams do
--      let type <- compileExpr val.type
--      let c := .quotient ⟨val.name, val.levelParams, type, val.kind⟩
--      let (anonAddr, metaAddr) ← hashConst c
--      modify fun stt => { stt with
--        axioms := (stt.axioms.insert const.name (anonAddr, metaAddr))
--        names := stt.names.insert const.name (anonAddr, metaAddr)
--      }
--      return (anonAddr, metaAddr)
--
--/-- compile possibly mutual Lean definition --/
--partial def compileDefinition (struct: PreDefinition)
--  : CompileM (Address × Address) := do
--  dbg_trace "compileDefinition {struct.name}"
--  -- If the mutual size is one, simply content address the single definition
--  if struct.all matches [_] then
--    let defn <- withMutCtx ({(struct.name,0)}) $ preDefinitionToIR struct
--    let (anonAddr, metaAddr) <- hashConst $ .definition defn
--    modify fun stt => { stt with
--      names := stt.names.insert struct.name (anonAddr, metaAddr)
--    }
--    return (anonAddr, metaAddr)
--  -- Collecting and sorting all definitions in the mutual block
--  let mut mutDefs : Array PreDefinition := #[]
--  for n in struct.all do
--    match <- findLeanConst n with
--      | .defnInfo x => mutDefs := mutDefs.push (mkPreDefinition x)
--      | .opaqueInfo x => mutDefs := mutDefs.push (mkPreOpaque x)
--      | .thmInfo x => mutDefs := mutDefs.push (mkPreTheorem x)
--      | x => throw $ .invalidConstantKind x.name "mutdef" x.ctorName
--  let mutualDefs <- sortDefs mutDefs.toList
--  let mutCtx := defMutCtx mutualDefs
--  let definitions ← withMutCtx mutCtx <|
--    mutualDefs.mapM (·.mapM preDefinitionToIR)
--  -- Building and storing the block
--  let (blockAnonAddr, blockMetaAddr) ← hashConst $ .mutual ⟨definitions⟩
--  modify fun stt =>
--    { stt with blocks := stt.blocks.insert (blockAnonAddr, blockMetaAddr) }
--  -- While iterating on the definitions from the mutual block, we need to track
--  -- the correct objects to return
--  let mut ret? : Option (Address × Address) := none
--  for name in struct.all do
--    -- Storing and caching the definition projection
--    -- Also adds the constant to the array of constants
--    let some idx := mutCtx.get? name | throw $ .cantFindMutDefIndex name
--    let (anonAddr, metaAddr) ←
--      hashConst $ .definitionProj ⟨name, blockAnonAddr, blockMetaAddr, idx⟩
--    modify fun stt => { stt with
--      names := stt.names.insert name (anonAddr, metaAddr)
--    }
--    if struct.name == name then ret? := some (anonAddr, metaAddr)
--  match ret? with
--  | some ret => return ret
--  | none => throw $ .constantNotContentAddressed struct.name
--
--partial def preDefinitionToIR (d: PreDefinition)
--  : CompileM Ix.Definition := withCurrent d.name $ withLevels d.levelParams do
--  dbg_trace "preDefinitionToIR {d.name}"
--  let typ <- compileExpr d.type
--  let val <- compileExpr d.value
--  return ⟨d.name, d.levelParams, typ, d.kind, val, d.hints, d.safety, d.all⟩
--
--partial def getRecursors (ind : Lean.InductiveVal) 
--  : CompileM (List Lean.RecursorVal) := do
--    return (<- get).env.constants.fold accRecr []
--    where
--      accRecr (acc: List Lean.RecursorVal) (n: Lean.Name) (c: Lean.ConstantInfo)
--        : List Lean.RecursorVal :=
--        match n with
--        | .str n ..
--        | .num n .. =>
--          if n == ind.name then match c with
--            | .recInfo r => r :: acc
--            | _ => acc
--          else acc
--        | _ => acc
--
--partial def makePreInductive (ind: Lean.InductiveVal) 
--  : CompileM Ix.PreInductive := do
--    dbg_trace "-> makePreInductive {ind.name}";
--    let ctors <- ind.ctors.mapM getCtor
--    let recrs <- getRecursors ind
--    return ⟨ind.name, ind.levelParams, ind.type, ind.numParams, ind.numIndices,
--      ind.all, ctors, recrs, ind.numNested, ind.isRec, ind.isReflexive, ind.isUnsafe⟩
--    where
--      getCtor (name: Lean.Name) : CompileM (Lean.ConstructorVal) := do
--        match (<- findLeanConst name) with
--        | .ctorInfo c => pure c
--        | _ => throw <| .invalidConstantKind name "constructor" ""
--
--/--
--Content-addresses an inductive and all inductives in the mutual block as a
--mutual block, even if the inductive itself is not in a mutual block.
--
--Content-addressing an inductive involves content-addressing its associated
--constructors and recursors, hence the complexity of this function.
---/
--partial def compileInductive (initInd: Lean.InductiveVal) 
--  : CompileM (Address × Address) := do
--  dbg_trace "-> compileInductive {initInd.name}";
--  let mut preInds := #[]
--  let mut nameData : Std.HashMap Lean.Name (List Lean.Name × List Lean.Name) := {}
--  -- collect all mutual inductives as Ix.PreInductives
--  for indName in initInd.all do
--    match ← findLeanConst indName with
--    | .inductInfo ind =>
--      let preInd <- makePreInductive ind
--      preInds := preInds.push preInd
--      nameData := nameData.insert indName (ind.ctors, preInd.recrs.map (·.name))
--    | const => throw $ .invalidConstantKind const.name "inductive" const.ctorName
--  -- sort PreInductives into equivalence classes
--  let mutualInds <- sortInds preInds.toList
--  let mutCtx := indMutCtx mutualInds
--  -- compile each preinductive with the mutCtx
--  let irInds ← withMutCtx mutCtx $ mutualInds.mapM (·.mapM preInductiveToIR)
--  let (blockAnonAddr, blockMetaAddr) ← hashConst $ .inductive ⟨irInds⟩
--  modify fun stt =>
--    { stt with blocks := stt.blocks.insert (blockAnonAddr, blockMetaAddr) }
--  -- While iterating on the inductives from the mutual block, we need to track
--  -- the correct objects to return
--  let mut ret? : Option (Address × Address) := none
--  for (indName, indIdx) in initInd.all.zipIdx do
--    -- Store and cache inductive projections
--    let name := indName
--    let (anonAddr, metaAddr) ←
--      hashConst $ .inductiveProj ⟨name, blockAnonAddr, blockMetaAddr, indIdx⟩
--    modify fun stt => { stt with
--      names := stt.names.insert name (anonAddr, metaAddr)
--    }
--    if name == initInd.name then ret? := some (anonAddr, metaAddr)
--    let some (ctors, recrs) := nameData.get? indName
--      | throw $ .cantFindMutDefIndex indName
--    for (ctorName, ctorIdx) in ctors.zipIdx do
--      -- Store and cache constructor projections
--      let (anonAddr, metaAddr) ←
--        hashConst $ .constructorProj
--          ⟨ctorName, blockAnonAddr, blockMetaAddr, indIdx, indName, ctorIdx⟩
--      modify fun stt => { stt with
--        names := stt.names.insert ctorName (anonAddr, metaAddr)
--      }
--    for (recrName, recrIdx) in recrs.zipIdx do
--      -- Store and cache recursor projections
--      let (anonAddr, metaAddr) ←
--        hashConst $ .recursorProj
--          ⟨recrName, blockAnonAddr, blockMetaAddr, indIdx, indName, recrIdx⟩
--      modify fun stt => { stt with
--        names := stt.names.insert recrName (anonAddr, metaAddr)
--      }
--  match ret? with
--  | some ret => return ret
--  | none => throw $ .constantNotContentAddressed initInd.name
--
--partial def preInductiveToIR (ind : Ix.PreInductive) : CompileM Ix.Inductive 
--  := withCurrent ind.name $ withLevels ind.levelParams $ do
--  dbg_trace "-> preInductiveToIR {ind.name}";
--  let (recs, ctors) := <- ind.recrs.foldrM (init := ([], [])) collectRecsCtors
--  let type <- compileExpr ind.type
--    -- NOTE: for the purpose of extraction, the order of `ctors` and `recs` MUST
--    -- match the order used in `mutCtx`
--  return ⟨ind.name, ind.levelParams, type, ind.numParams, ind.numIndices,
--    ind.all, ctors, recs, ind.numNested, ind.isRec, ind.isReflexive, ind.isUnsafe⟩
--  where
--    collectRecsCtors
--      : Lean.RecursorVal
--      -> List Recursor × List Constructor 
--      -> CompileM (List Recursor × List Constructor)
--      | r, (recs, ctors) =>
--        if isInternalRec r.type ind.name then do
--          let (thisRec, thisCtors) <- internalRecToIR (ind.ctors.map (·.name)) r
--          pure (thisRec :: recs, thisCtors)
--        else do
--          let thisRec ← externalRecToIR r
--          pure (thisRec :: recs, ctors)
--
--partial def internalRecToIR (ctors : List Lean.Name) (recr: Lean.RecursorVal)
--  : CompileM (Ix.Recursor × List Ix.Constructor) :=
--  withCurrent recr.name $ withLevels recr.levelParams do
--    dbg_trace s!"internalRecToIR"
--    let typ ← compileExpr recr.type
--    let (retCtors, retRules) ← recr.rules.foldrM (init := ([], []))
--      fun r (retCtors, retRules) => do
--        if ctors.contains r.ctor then
--          let (ctor, rule) ← recRuleToIR r
--          pure $ (ctor :: retCtors, rule :: retRules)
--        else pure (retCtors, retRules) -- this is an external recursor rule
--    let recr := ⟨recr.name, recr.levelParams, typ, recr.numParams, recr.numIndices,
--      recr.numMotives, recr.numMinors, retRules, recr.k, recr.isUnsafe⟩
--    return (recr, retCtors)
--
--partial def externalRecToIR (recr: Lean.RecursorVal): CompileM Recursor :=
--  withCurrent recr.name $ withLevels recr.levelParams do
--    dbg_trace s!"externalRecToIR"
--    let typ ← compileExpr recr.type
--    let rules ← recr.rules.mapM externalRecRuleToIR
--    return ⟨recr.name, recr.levelParams, typ, recr.numParams, recr.numIndices,
--      recr.numMotives, recr.numMinors, rules, recr.k, recr.isUnsafe⟩
--
--partial def recRuleToIR (rule : Lean.RecursorRule)
--  : CompileM (Ix.Constructor × Ix.RecursorRule) := do
--  dbg_trace s!"recRuleToIR"
--  let rhs ← compileExpr rule.rhs
--  match ← findLeanConst rule.ctor with
--  | .ctorInfo ctor => withCurrent ctor.name $ withLevels ctor.levelParams do
--    let typ ← compileExpr ctor.type
--    let ctor :=
--      ⟨ctor.name, ctor.levelParams, typ, ctor.cidx, ctor.numParams, ctor.numFields, ctor.isUnsafe⟩
--    pure (ctor, ⟨rule.ctor, rule.nfields, rhs⟩)
--  | const =>
--    throw $ .invalidConstantKind const.name "constructor" const.ctorName
--
--partial def externalRecRuleToIR (rule : Lean.RecursorRule) 
--  : CompileM RecursorRule :=
--  return ⟨rule.ctor, rule.nfields, ← compileExpr rule.rhs⟩
--
--/--
--Content-addresses a Lean expression and adds it to the store.
--
--Constants are the tricky case, for which there are two possibilities:
--* The constant belongs to `mutCtx`, representing a recursive call. Those are
--encoded as `.rec_` with indexes based on order in the mutual definition
--* The constant doesn't belong to `mutCtx`, meaning that it's not a recursion
--and thus we can canon the actual constant right away
---/
--partial def compileExpr : Lean.Expr → CompileM Expr
--| .bvar idx => do match (← read).bindCtx[idx]? with
--  -- Bound variables must be in the bind context
--  | some _ => return .var idx
--  | none => throw $ .invalidBVarIndex idx
--| .sort lvl => return .sort $ ← compileLevel lvl
--| .const name lvls => do
--  let univs ← lvls.mapM compileLevel
--  match (← read).mutCtx.get? name with
--  -- recursing!
--  | some i => return .rec_ name i univs
--  | none => match (<- get).comms.get? name with
--    | some (commAddr, metaAddr) => do
--      return .const name commAddr metaAddr univs
--    | none => do
--      let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
--      return .const name contAddr metaAddr univs
--| .app fnc arg => return .app (← compileExpr fnc) (← compileExpr arg)
--| .lam name typ bod info =>
--  return .lam name info (← compileExpr typ) (← withBinder name $ compileExpr bod)
--| .forallE name dom img info =>
--  return .pi name info (← compileExpr dom) (← withBinder name $ compileExpr img)
--| .letE name typ exp bod nD =>
--  return .letE name (← compileExpr typ) (← compileExpr exp)
--    (← withBinder name $ compileExpr bod) nD
--| .lit lit => return .lit lit
--| .proj name idx exp => do
--  let (contAddr, metaAddr) ← compileConst (← findLeanConst name)
--  return .proj name contAddr metaAddr idx (← compileExpr exp)
--| expr@(.fvar ..)  => throw $ .freeVariableExpr expr
--| expr@(.mvar ..)  => throw $ .metaVariableExpr expr
---- TODO: cursed
--| (.mdata _ x) => compileExpr x
--
--/--
--A name-irrelevant ordering of Lean expressions.
---/
--partial def compareExpr (ctx: Std.HashMap Lean.Name Nat)
--  (xlvls ylvls: List Lean.Name)
--  --: Lean.Expr → Lean.Expr → CompileM SOrder
--  (x y: Lean.Expr) : CompileM SOrder := do
--  --dbg_trace "compareExpr {repr xlvls} {repr ylvls} {repr x} {repr y}"
--  --let mutCtx := (<- read).mutCtx
--  --dbg_trace "mutCtx {repr mutCtx}";
--  match x, y with
--  | e@(.mvar ..), _ => throw $ .unfilledExprMetavariable e
--  | _, e@(.mvar ..) => throw $ .unfilledExprMetavariable e
--  | e@(.fvar ..), _ => throw $ .freeVariableExpr e
--  | _, e@(.fvar ..) => throw $ .freeVariableExpr e
--  | .mdata _ anonmdata _ y  => compareExpr ctx xlvls ylvls x y
--  | .mdata _ x, y  => compareExpr ctx xlvls ylvls x y
--  | x, .mdata _ y  => compareExpr ctx xlvls ylvls x y
--  | .bvar x, .bvar y => return ⟨true, compare x y⟩
--  | .bvar .., _ => return ⟨true, .lt⟩
--  | _, .bvar .. => return ⟨true, .gt⟩
--  | .sort x, .sort y => compareLevel xlvls ylvls x y
--  | .sort .., _ => return ⟨true, .lt⟩
--  | _, .sort .. => return ⟨true, .gt⟩
--  | .const x xls, .const y yls => do
--    --dbg_trace "compare const {x} {y}";
--    let univs ← SOrder.zipM (compareLevel xlvls ylvls) xls yls
--    if univs.ord != .eq then return univs
--    --dbg_trace "compare const {x} {y} {repr ctx}";
--    match ctx.get? x, ctx.get? y with
--    | some nx, some ny => return ⟨false, compare nx ny⟩
--    | none, some _ => do
--      return ⟨true, .gt⟩
--    | some _, none =>
--      return ⟨true, .lt⟩
--    | none, none =>
--      if x == y then 
--        return ⟨true, .eq⟩
--      else do
--        let x' <- compileConst $ ← findLeanConst x
--        let y' <- compileConst $ ← findLeanConst y
--        return ⟨true, compare x' y'⟩
--  | .const .., _ => return ⟨true, .lt⟩
--  | _, .const .. => return ⟨true, .gt⟩
--  | .app xf xa, .app yf ya =>
--    SOrder.cmpM 
--      (compareExpr ctx xlvls ylvls xf yf) 
--      (compareExpr ctx xlvls ylvls xa ya)
--  | .app .., _ => return ⟨true, .lt⟩
--  | _, .app .. => return ⟨true, .gt⟩
--  | .lam _ xt xb _, .lam _ yt yb _ => 
--    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
--  | .lam .., _ => return ⟨true, .lt⟩
--  | _, .lam .. => return ⟨true, .gt⟩
--  | .forallE _ xt xb _, .forallE _ yt yb _ => 
--    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
--  | .forallE .., _ => return ⟨true, .lt⟩
--  | _, .forallE .. => return ⟨true, .gt⟩
--  | .letE _ xt xv xb _, .letE _ yt yv yb _ =>
--    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) <|
--    SOrder.cmpM (compareExpr ctx xlvls ylvls xv yv)
--      (compareExpr ctx xlvls ylvls xb yb)
--  | .letE .., _ => return ⟨true, .lt⟩
--  | _, .letE .. => return ⟨true, .gt⟩
--  | .lit x, .lit y => return ⟨true, compare x y⟩
--  | .lit .., _ => return ⟨true, .lt⟩
--  | _, .lit .. => return ⟨true, .gt⟩
--  | .proj _ nx tx, .proj _ ny ty => 
--    SOrder.cmpM (pure ⟨true, compare nx ny⟩) 
--      (compareExpr ctx xlvls ylvls tx ty)
--
--/-- AST comparison of two Lean definitions. --/
--partial def compareDef (ctx: Std.HashMap Lean.Name Nat) (x y: PreDefinition) : CompileM Ordering := do
--  let key := match compare x.name y.name with
--    | .lt => (x.name, y.name)
--    | _ => (y.name, x.name)
--  match (<- get).eqConst.get? key with
--  | some o => return o
--  | none => do
--    let sorder <- SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
--      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
--      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type)
--        (compareExpr ctx x.levelParams y.levelParams x.value y.value)
--    if sorder.strong then modify fun stt => { stt with
--        eqConst := stt.eqConst.insert key sorder.ord
--      }
--    return sorder.ord
--
--/--
--`sortDefs` recursively sorts a list of mutual definitions into equivalence classes.
--At each stage, we take as input the current best known equivalence
--classes (held in the `mutCtx` of the CompileEnv). For most cases, equivalence
--can be determined by syntactic differences which are invariant to the current
--best known classification. For example:
--
--```
--mutual
--  def : Nat := 1
--  def bar : Nat := 2
--end
--```
--
--are both different due to the different values in the definition. We call this a
--"strong" ordering, and comparisons between defintions that produce strong
--orderings are cached across compilation.
--
--However, there are also weak orderings, where the order of definitions in a
--mutual block depends on itself.
--
--```
--mutual
--  def A : Nat → Nat
--  | 0 => 0
--  | n + 1 => B n + C n + 1
--
--  def B : Nat → Nat
--  | 0 => 0
--  | n + 1 => C n + 1
--
--  def C : Nat → Nat
--  | 0 => 0
--  | n + 1 => A n + 1
--end
--```
--
--Here since any reference to A, B, C has to be compiled into an index, the
--ordering chosen for A, B, C will effect itself, since we compile into
--something that looks, with order [A, B, C] like:
--
--```
--mutual
--  def #1 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #2 n + #3 n + 1
--
--  def #2 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #3 n + 1
--
--  def #3 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #1 n + 1
--end
--```
--
--This is all well and good, but if we chose order `[C, B, A]` then the block
--would compile as
--
--```
--mutual
--  def #1 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #3 n + 1
--
--  def #2 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #1 n + 1
--
--  def #3 : Nat → Nat
--  | 0 => 0
--  | n + 1 => #2 n + #1 n + 1
--end
--```
--
--with completely different hashes. So we need to figure out a canonical order for
--such mutual blocks.
--
--We start by assuming that all definitions in a mutual block are equal and then 
--recursively refining this assumption through successive sorting passes. This
--algorithm bears some similarity to partition refinement:
--```
--classes₀ := [startDefs]
--classes₁ := sortDefs classes₀
--classes₂ := sortDefs classes₁
--classes₍ᵢ₊₁₎ := sortDefs classesᵢ ...
--```
--Initially, `startDefs` is simply the list of definitions we receive from
--`DefinitionVal.all`, sorted by name. We assume that at we will reach some
--fixed-point where `classes₍ᵢ₊₁₎ := classesᵢ` and no further refinement is
--possible (we have not rigourously proven such a fixed point exists, but
--it seams reasonable given that after the first pass to find the strongly ordered
--definitions, the algorithm should only separate partitions into smaller ones)
---/
--partial def sortDefs (classes : List PreDefinition)
--  : CompileM (List (List PreDefinition)) := do
--    sortDefsInner [List.sortBy (compare ·.name ·.name) classes] 0
--  where
--    eqDef (ctx: Std.HashMap Lean.Name Nat) (x y: PreDefinition) 
--      : CompileM Bool := (· == .eq) <$> compareDef ctx x y
--    sortDefsInner (classes: List (List PreDefinition)) (iter: Nat)
--      : CompileM (List (List PreDefinition)) := do
--      let ctx := defMutCtx classes
--      dbg_trace "sortdefs {iter} classes {repr (classes.map (·.map (·.name)))}";
--      let newClasses ← classes.mapM fun ds =>
--        match ds with
--        | []  => unreachable!
--        | [d] => pure [[d]]
--        | ds  => do pure $ (← List.groupByM (eqDef ctx) $ ← ds.sortByM (compareDef ctx))
--      let newClasses := newClasses.flatten.map (List.sortBy (compare ·.name ·.name))
--      if classes == newClasses then return newClasses
--      else sortDefsInner newClasses (iter + 1)
--
--/-- AST comparison of two Lean inductives. --/
--partial def compareInd (ctx: Std.HashMap Lean.Name Nat) (x y: PreInductive) 
--  : CompileM Ordering := do
--  --dbg_trace "compareInd {x.name} {y.name}";
--  let key := match compare x.name y.name with
--    | .lt => (x.name, y.name)
--    | _ => (y.name, x.name)
--  match (<- get).eqConst.get? key with
--  | some o => return o
--  | none => do
--    let sorder <- do
--      SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
--      SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
--      SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
--      SOrder.cmpM (pure ⟨true, compare x.ctors.length y.ctors.length⟩) <|
--      SOrder.cmpM (pure ⟨true, compare x.recrs.length y.recrs.length⟩) <|
--      SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
--      SOrder.cmpM (SOrder.zipM compareCtor x.ctors y.ctors)
--        (SOrder.zipM compareRecr x.recrs y.recrs)
--    if sorder.strong then modify fun stt => { stt with
--        eqConst := stt.eqConst.insert key sorder.ord
--      }
--    --dbg_trace "compareInd {x.name} {y.name} -> {repr sorder.ord}";
--    return sorder.ord
--  where
--    compareCtor (x y: Lean.ConstructorVal) : CompileM SOrder := do
--     --dbg_trace "compareCtor {x.name} {y.name}";
--      let key := match compare x.name y.name with
--        | .lt => (x.name, y.name)
--        | _ => (y.name, x.name)
--      match (<- get).eqConst.get? key with
--      | some o => return ⟨true, o⟩
--      | none => do
--      let sorder <- do
--        SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
--        SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
--        SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
--        SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩) <|
--          (compareExpr ctx x.levelParams y.levelParams x.type y.type)
--      if sorder.strong then modify fun stt => { stt with
--          eqConst := stt.eqConst.insert key sorder.ord
--        }
--      return sorder
--    compareRecr (x y: Lean.RecursorVal) : CompileM SOrder := do
--      --dbg_trace "compareRecr {x.name} {y.name}";
--      let key := match compare x.name y.name with
--        | .lt => (x.name, y.name)
--        | _ => (y.name, x.name)
--      match (<- get).eqConst.get? key with
--      | some o => return ⟨true, o⟩
--      | none => do
--      let sorder <- do
--        SOrder.cmpM (pure ⟨true, compare x.levelParams.length y.levelParams.length⟩) <|
--        SOrder.cmpM (pure ⟨true,compare x.numParams y.numParams⟩) <|
--        SOrder.cmpM (pure ⟨true,compare x.numIndices y.numIndices⟩) <|
--        SOrder.cmpM (pure ⟨true, compare x.numMotives y.numMotives⟩) <|
--        SOrder.cmpM (pure ⟨true,compare x.numMinors y.numMinors⟩) <|
--        SOrder.cmpM (pure ⟨true, compare x.k y.k⟩) <|
--        SOrder.cmpM (compareExpr ctx x.levelParams y.levelParams x.type y.type) <|
--          (SOrder.zipM (compareRule x.levelParams y.levelParams) x.rules y.rules)
--      if sorder.strong then modify fun stt => { stt with
--          eqConst := stt.eqConst.insert key sorder.ord
--        }
--      return sorder
--    compareRule (xlvls ylvls: List Lean.Name) (x y: Lean.RecursorRule)
--      : CompileM SOrder := do
--        SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩)
--          (compareExpr ctx xlvls ylvls x.rhs y.rhs)
--
----#check List.sortBy (compare ·.name ·.name) [`Test.Ix.Inductives.C, `Test.Ix.Inductives.A, `Test.Ix.Inductives.B]
--
--/-- `sortInds` recursively sorts a list of inductive datatypes into equivalence
--classes, analogous to `sortDefs`
----/
--partial def sortInds (classes : (List PreInductive)) 
--  : CompileM (List (List PreInductive)) := do
--    sortIndsInner [List.sortBy (compare ·.name ·.name) classes] 0
--  where
--    eqInd (ctx: Std.HashMap Lean.Name Nat) (x y: PreInductive) : CompileM Bool
--      := (· == .eq) <$> compareInd ctx x y
--    sortIndsInner (classes: List (List PreInductive)) (iter: Nat)
--      : CompileM (List (List PreInductive)) := do
--      dbg_trace "sortInds {iter} classes {repr (classes.map (·.map (·.name)))}";
--      let ctx := indMutCtx classes
--      let newClasses ← classes.mapM fun ds =>
--        match ds with
--        | []  => unreachable!
--        | [d] => pure [[d]]
--        | ds  => do pure $ (← List.groupByM (eqInd ctx) $ ← ds.sortByM (compareInd ctx))
--      let newClasses := newClasses.flatten.map (List.sortBy (compare ·.name ·.name))
--      if classes == newClasses then return newClasses
--      else sortIndsInner newClasses (iter + 1)
--
--end
--
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
--    let maxHeartBeats <- (·.maxHeartBeats) <$> read
--    let decl := Lean.Declaration.defnDecl defn
--    match Lean.Environment.addDeclCore env maxHeartBeats decl .none with
--    | .ok e => do
--      modify fun stt => { stt with env := e }
--      return ()
--    | .error e => throw $ .kernelException e
--
--partial def addDef
--  (lvls: List Lean.Name)
--  (typ val: Lean.Expr)
--  : CompileM (Address × Address) := do
--  let typ' <- compileExpr typ
--  let val' <- compileExpr val
--  let anonConst := Ix.Const.definition 
--    ⟨.anonymous, lvls, typ', .definition, val', .opaque, .safe, []⟩
--  let (anonIxon,_) <- dematerializeConst anonConst
--  let anonAddr <- storeConst anonIxon
--  let name := anonAddr.toUniqueName
--  let const := 
--    Ix.Const.definition ⟨name, lvls, typ', .definition, val', .opaque, .safe, []⟩
--  let (a, m) <- hashConst const
--  if a != anonAddr then
--    throw <| .alphaInvarianceFailure anonConst anonAddr const a
--  else
--    tryAddLeanDef (makeLeanDef a.toUniqueName lvls typ val)
--    return (a, m)
--
--partial def commitConst (anon meta: Address)
--  : CompileM (Address × Address) := do
--  let secret <- freshSecret
--  let comm := .comm ⟨secret, anon⟩
--  let commAddr <- storeConst comm
--  let commMeta := .comm ⟨secret, meta⟩
--  let commMetaAddr <- storeConst commMeta
--  modify fun stt => { stt with
--    comms := stt.comms.insert commAddr.toUniqueName (commAddr, commMetaAddr)
--  }
--  return (commAddr, commMetaAddr)
--
--partial def commitDef 
--  (lvls: List Lean.Name) 
--  (typ val: Lean.Expr)
--  : CompileM (Address × Address) := do
--  let (a, m) <- addDef lvls typ val
--  let (ca, cm) <- commitConst a m
--  tryAddLeanDef (makeLeanDef ca.toUniqueName lvls typ val)
--  --tryAddLeanDecl (makeLeanDef ca.toUniqueName lvls typ (mkConst a.toUniqueName []))
--  return (ca, cm)
--
--
--partial def packLevel (lvls: Nat) (commit: Bool): CompileM Address :=
--  match Ixon.natPackAsAddress lvls with
--  | some lvlsAddr => do
--    if commit then
--      let secret <- freshSecret
--      let comm := .comm (Ixon.Comm.mk secret lvlsAddr)
--      let commAddr <- storeConst comm
--      modify fun stt => { stt with
--        comms := stt.comms.insert commAddr.toUniqueName (commAddr, commAddr)
--      }
--      return commAddr
--    else return lvlsAddr
--  | .none => throw $ .cantPackLevel lvls
--
--partial def checkClaim
--  (const: Lean.Name)
--  (type: Lean.Expr)
--  (sort: Lean.Expr)
--  (lvls: List Lean.Name)
--  (commit: Bool)
--  : CompileM (Claim × Address × Address) := do
--  let leanConst <- findLeanConst const
--  let (value, valMeta) <- compileConst leanConst >>= comm
--  let (type, typeMeta) <- addDef lvls sort type >>= comm
--  let lvls <- packLevel lvls.length commit
--  return (Claim.checks (CheckClaim.mk lvls type value), typeMeta, valMeta)
--  where
--    comm a := if commit then commitConst (Prod.fst a) (Prod.snd a) else pure a
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
--
--/--
--Content-addresses the "delta" of an environment, that is, the content that is
--added on top of the imports.
--
--Important: constants with open references in their expressions are filtered out.
--Open references are variables that point to names which aren't present in the
--`Lean.ConstMap`.
---/
--def compileDelta (delta : Lean.PersistentHashMap Lean.Name Lean.ConstantInfo)
--  : CompileM Unit := delta.forM fun _ c => discard $ compileConst c
--
--def compileEnv (env: Lean.Environment)
--  : CompileM Unit := do
--  compileDelta env.getDelta
--  env.getConstMap.forM fun _ c => if !c.isUnsafe then discard $ compileConst c else pure ()
--
--def CompileM.runIO (c : CompileM α) 
--  (env: Lean.Environment)
--  (maxHeartBeats: USize := 200000)
--  (seed : Option Nat := .none)
--  : IO (α × CompileState) := do
--  let seed <- match seed with
--    | .none => IO.monoNanosNow
--    | .some s => pure s
--  match <- c.run (.init maxHeartBeats) (.init env seed) with
--  | (.ok a, stt) => return (a, stt)
--  | (.error e, _) => throw (IO.userError (<- e.pretty))
--
--def CompileM.runIO' (c : CompileM α) 
--  (stt: CompileState)
--  (maxHeartBeats: USize := 200000)
--  : IO (α × CompileState) := do
--  match <- c.run (.init maxHeartBeats) stt with
--  | (.ok a, stt) => return (a, stt)
--  | (.error e, _) => throw (IO.userError (<- e.pretty))
--
--def compileEnvIO (env: Lean.Environment) : IO (CompileState):= do
--  Prod.snd <$> (compileDelta env.getDelta).runIO env
