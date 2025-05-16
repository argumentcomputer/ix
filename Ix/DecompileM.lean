import Batteries.Data.RBMap
import Ix.TransportM
import Ix.Ixon.Metadata
import Ix.Ixon.Const
import Ix.Ixon.Serialize
import Ix.Common
import Ix.Store
import Ix.CompileM

open Batteries (RBMap)
open Batteries (RBSet)
open Ix.TransportM
open Ix.Compile

namespace Ix.Decompile

/- the current Ix constant being decompiled -/
structure Named where
  name: Lean.Name
  cont: Address
  meta: Address
deriving Inhabited, Repr

instance : ToString Named where
  toString n := s!"{n.cont}:{n.meta}-{n.name}"

/- The local environment for the Ix -> Lean4 decompiler -/
structure DecompileEnv where
  names : RBMap Lean.Name (Address × Address) compare
  store : RBMap Address Ixon.Const compare
  univCtx : List Lean.Name
  bindCtx : List Lean.Name
  mutCtx  : RBMap Lean.Name Nat compare
  current: Named

/- initialize from an Ixon store and a name-index to the store -/
def DecompileEnv.init
  (names : RBMap Lean.Name (Address × Address) compare)
  (store : RBMap Address Ixon.Const compare)
  : DecompileEnv
  := ⟨names, store, default, default, default, default⟩

/- a collection of an inductive datatype with its constructors and recursors -/
structure InductiveBlock where
  val: Lean.ConstantInfo
  ctors: List Lean.ConstantInfo
  recrs: List Lean.ConstantInfo
deriving Repr

def InductiveBlock.contains (i: InductiveBlock) (name: Lean.Name) : Bool := 
  i.val.name == name ||
  i.ctors.any (fun c => c.name == name) ||
  i.recrs.any (fun r => r.name == name)

/- A Block is one of the possible sets of Lean constants we could generate
 from a pair of content and metadata Ix addresses -/
inductive Block where
| single : Lean.ConstantInfo -> Block
| mutual : List Lean.ConstantInfo -> Block
| inductive : InductiveBlock -> Block
| mutualInductive : List InductiveBlock -> Block
deriving Repr

def Block.contains (name: Lean.Name) : Block -> Bool
| .single const => const.name == name
| .mutual consts => consts.any (fun c => c.name == name)
| .inductive i => i.contains name
| .mutualInductive is => is.any (fun i => i.contains name)

/- The name of an inductive datatype with the names of its constructors and
recursors. Used to create a BlockNames struct.
-/
structure InductiveBlockNames where
  val: Lean.Name
  ctors: List Lean.Name
  recrs: List Lean.Name
deriving Repr

def InductiveBlockNames.contains (i: InductiveBlockNames) (name: Lean.Name) : Bool := 
  i.val == name ||
  i.ctors.any (fun c => c == name) ||
  i.recrs.any (fun r => r == name)

/- A BlockNames struct is the names of a Block. Naively, the decompiler
operates by mapping content-address pairs to blocks, but since each block might
be mapped onto by many address pairs, we only record address pair to BlockNames
mapping, and separately keep a single level map of Lean.Name to
Lean.ConstantInfo
-/
inductive BlockNames where
| single : Lean.Name -> BlockNames
| mutual : List Lean.Name -> BlockNames
| inductive : InductiveBlockNames -> BlockNames
| mutualInductive : List InductiveBlockNames -> BlockNames
deriving Repr

def BlockNames.contains (name: Lean.Name) : BlockNames -> Bool
| .single const => const == name
| .mutual consts => consts.any (fun c => c == name)
| .inductive i => i.contains name
| .mutualInductive is => is.any (fun i => i.contains name)

structure DecompileState where
  constants: RBMap Lean.Name Lean.ConstantInfo compare
  blocks : RBMap (Address × Address) BlockNames compare
  deriving Inhabited

inductive DecompileError
| freeLevel (curr: Named) (ctx: List Lean.Name) (lvl: Lean.Name) (idx: Nat)
| mismatchedLevelName
  (curr: Named) (ctx: List Lean.Name) (got: Lean.Name)
  (exp: Lean.Name) (idx: Nat)
| invalidBVarIndex (curr: Named) (ctx: List Lean.Name) (idx: Nat)
| mismatchedMutIdx
  (curr: Named) (ctx: RBMap Lean.Name Nat compare) (exp: Lean.Name) 
  (idx: Nat) (got: Nat)
| unknownMutual 
  (curr: Named) (ctx: RBMap Lean.Name Nat compare) (exp: Lean.Name) (idx: Nat)
| transport (curr: Named) (err: TransportError) (cont meta: Address)
| unknownName (curr: Named) (name: Lean.Name)
| unknownStoreAddress (curr: Named) (exp: Address)
| expectedIxonMetadata (curr: Named) (exp: Address) (got: Ixon.Const)
| badProjection
  (curr: Named) (name: Lean.Name) (cont meta: Address) (msg: String)
| nonCongruentInductives (curr: Named) (x y: Ix.Inductive)
| nameNotInBlockNames
  (curr: Named) (block: BlockNames) (name: Lean.Name) (cont meta: Address)
| nameNotInBlock
  (curr: Named) (block: Block) (name: Lean.Name) (cont meta: Address)
| mismatchedName
  (curr: Named) (exp: Lean.Name) (got: Lean.Name) (cont meta: Address)
| expectedNameInBlock
  (curr: Named) (exp: Lean.Name) (got: BlockNames) (cont meta: Address)
| expectedDefnBlock (curr: Named) (exp: Lean.Name) (got: Block) (cont meta: Address)
| expectedMutDefBlock (curr: Named) (got: BlockNames) (cont meta: Address)
| expectedMutIndBlock (curr: Named) (got: BlockNames) (cont meta: Address)
| expectedMutIndConst (curr: Named) (got: Ix.Const) (cont meta: Address)
| expectedMutDefConst (curr: Named) (got: Ix.Const) (cont meta: Address)
| overloadedConstants (curr: Named) (x y: Lean.ConstantInfo)
| todo
deriving Repr


def DecompileError.pretty : DecompileError -> String
| .freeLevel c lvls n i => s!"Free level {n} at {i} with ctx {repr lvls} @ {c}"
| .mismatchedLevelName c ctx n' n i => 
  s!"Expected level name {n} at index {i} but got {n'} with context {repr ctx} @ {c}"
| .invalidBVarIndex c ctx i => 
  s!"Bound variable {i} escapes context {ctx} @ {c}"
| .mismatchedMutIdx c ctx n i i' => 
  s!"expected mutual recusion index {i} at name {n} but got {i'} with context {repr ctx} @ {c}"
| .unknownMutual c ctx n i => 
  s!"unknown mutual name {n} with expected index {i} with context {repr ctx} @ {c}"
| .transport curr e c m => s!"decompiler transport error {e} at {c} {m} @ {curr}"
| .unknownName c n => s!"unknown name {n} @ {c}"
| .unknownStoreAddress c x => s!"unknown store address {x} @ {c}"
| .expectedIxonMetadata c x ixon => s!"expected metadata at address {x}, got {repr ixon} @ {c}"
| .badProjection curr n c m s => s!"bad projection {n} at address {c}:{m}, {s} @ {curr}"
| .nonCongruentInductives c x y  => s!"noncongruent inductives {repr x} {repr y} @ {c}"
| .nameNotInBlockNames curr b n c m  => s!"expected block names {repr b} at {c}:{m} to contain {n} @ {curr}"
| .nameNotInBlock curr b n c m  => s!"expected block {repr b} at {c}:{m} to contain {n} @ {curr}"
| .mismatchedName curr e g c m => 
  s!"expected name {e}, got {g} at address {c} {m} @ {curr}"
| .expectedNameInBlock curr e b c m => 
  s!"expected name {e} in block {repr b} at address {c} {m} @ {curr}"
| .expectedDefnBlock curr e g c m =>
  s!"expected definition named {e}, got {repr g} at address {c} {m} @ {curr}"
| .expectedMutDefBlock curr g c m =>
  s!"expected mutual definition block, got {repr g} at address {c} {m} @ {curr}"
| .expectedMutIndBlock curr g c m =>
  s!"expected mutual inductive block, got {repr g} at address {c} {m} @ {curr}"
| .expectedMutIndConst curr g c m =>
  s!"expected mutual inductive constant, got {repr g} at address {c} {m} @ {curr}"
| .expectedMutDefConst curr g c m =>
  s!"expected mutual definition constant, got {repr g} at address {c} {m} @ {curr}"
| .overloadedConstants curr x y => 
  s!"overloaded constants, tried to overwrite {repr y} with {repr x} @ {curr}"
| .todo => s!"todo"

abbrev DecompileM := ReaderT DecompileEnv <| EStateM DecompileError DecompileState

def DecompileM.run (env: DecompileEnv) (stt: DecompileState) (c : DecompileM α)
  : EStateM.Result DecompileError DecompileState α
  := EStateM.run (ReaderT.run c env) stt

-- add binding name to local context
def withBinder (name: Lean.Name) : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def withLevels (lvls : List Lean.Name) : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with univCtx := lvls }

-- add mutual recursion info to local context
def withMutCtx (mutCtx : RBMap Lean.Name Nat compare) 
  : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with mutCtx := mutCtx }

def withNamed (name: Lean.Name) (cont meta: Address)
  : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with current := ⟨name, cont, meta⟩ }

-- reset local context
def resetCtx : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with univCtx := [], bindCtx := [], mutCtx := .empty }

def resetCtxWithLevels (lvls: List Lean.Name) : DecompileM α -> DecompileM α :=
  withReader $ fun c => { c with univCtx := lvls, bindCtx := [], mutCtx := .empty }

def decompileLevel: Ix.Level → DecompileM Lean.Level
| .zero => pure .zero
| .succ u => .succ <$> decompileLevel u
| .max a b => Lean.Level.max  <$> decompileLevel a <*> decompileLevel b
| .imax a b => Lean.Level.imax <$> decompileLevel a <*> decompileLevel b
| .param n i => do
  let env <- read
  match env.univCtx[i]? with
  | some n' =>
    if n == n' then pure (Lean.Level.param n)
    else throw (.mismatchedLevelName env.current env.univCtx n' n i)
  | none => throw <| .freeLevel env.current env.univCtx n i

partial def insertConst
  (const: Lean.ConstantInfo)
  : DecompileM Lean.Name := do
  match (<- get).constants.find? const.name with
  | .some const' =>
      if const == const' then return const.name
      else throw <| .overloadedConstants (<- read).current const const'
  | .none => modify fun stt => 
    { stt with constants := stt.constants.insert const.name const }
    return const.name

partial def insertBlock (c m: Address) (b: Block) : DecompileM BlockNames := do
  let bn <- match b with
    | .single const => .single <$> insertConst const
    | .mutual cs => .mutual <$> cs.mapM insertConst
    | .inductive i => .inductive <$> insertInductive i
    | .mutualInductive is => .mutualInductive <$> is.mapM insertInductive
  modifyGet fun stt =>
    (bn, { stt with blocks := stt.blocks.insert (c, m) bn })
  where
    insertInductive (i: InductiveBlock) : DecompileM InductiveBlockNames := do
      let val <- insertConst i.val
      let ctors <- i.ctors.mapM insertConst
      let recrs <- i.recrs.mapM insertConst
      return ⟨val, ctors, recrs⟩

--mutual
--
--partial def decompileExpr: Ix.Expr → DecompileM Lean.Expr
--| .var i      => do match (← read).bindCtx[i]? with
--  | some _ => return .bvar i
--  | none => throw <| .invalidBVarIndex (<-read).current (<-read).bindCtx i
--| .sort u     => Lean.Expr.sort <$> decompileLevel u
--| .lit l      => pure (.lit l)
--| .app f a    => Lean.mkApp <$> decompileExpr f <*> decompileExpr a
--| .lam n bi t b =>
--    Lean.mkLambda n bi <$> decompileExpr t <*> withBinder n (decompileExpr b)
--| .pi n bi t b =>
--    Lean.mkForall n bi <$> decompileExpr t <*> withBinder n (decompileExpr b)
--| .letE n t v b nd =>
--    (@Lean.mkLet n)
--      <$> decompileExpr t
--      <*> decompileExpr v
--      <*> withBinder n (decompileExpr b)
--      <*> pure nd
--| .proj n cont meta i e => do
--    let _ <- ensureBlock n cont meta
--    Lean.mkProj n i <$> decompileExpr e
--| .const n cont meta us => do
--    let _ <- ensureBlock n cont meta
--    return Lean.mkConst n (<- us.mapM decompileLevel)
--| .rec_ n i us => do match (<- read).mutCtx.find? n with
--  | some i' =>
--    if i == i' then return Lean.mkConst n (<- us.mapM decompileLevel)
--    else throw <| .mismatchedMutIdx (<- read).current (<- read).mutCtx n i i'
--  | none => throw <| .unknownMutual (<- read).current (<- read).mutCtx n i
--
--partial def ensureBlock (name: Lean.Name) (c m: Address) : DecompileM BlockNames := do
--  match (<- get).blocks.find? (c, m) with
--  | .some b =>
--    if b.contains name then pure b
--    else throw <| .nameNotInBlockNames (<- read).current b name c m
--  | .none =>
--    let cont : Ixon.Const <- match (<- read).store.find? c with
--      | .some ixon => pure ixon
--      | .none => throw <| .unknownStoreAddress (<- read).current c
--    let meta : Ixon.Metadata <- match (<- read).store.find? m with
--      | .some (.meta meta) => pure meta
--      | .some x => throw <| .expectedIxonMetadata (<- read).current m x
--      | .none => throw <| .unknownStoreAddress (<- read).current m
--    match rematerialize cont meta with
--    | .ok const  => do
--      let blockNames <- withNamed name c m <| decompileConst const
--      if !blockNames.contains name then
--         throw <| .nameNotInBlockNames (<- read).current blockNames name c m
--      return blockNames
--    | .error e => throw (.transport (<- read).current e c m)
--
--partial def decompileDefn (x: Ix.Definition)
--  : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
--    let type <- decompileExpr x.type
--    let val <- decompileExpr x.value
--    let safety := if x.isPartial then .«partial» else .safe
--    match x.mode with
--    | .definition => return .defnInfo <|
--      Lean.mkDefinitionValEx x.name x.levelParams type val x.hints safety x.all
--    | .opaque => return .opaqueInfo <|
--      Lean.mkOpaqueValEx x.name x.levelParams type val true x.all
--    | .theorem => return .thmInfo <|
--      Lean.mkTheoremValEx x.name x.levelParams type val x.all
--
--partial def decompileIndc (x: Ix.Inductive)
--  : DecompileM
--    (Lean.ConstantInfo × List Lean.ConstantInfo × List Lean.ConstantInfo)
--    := withLevels x.levelParams do
--      let type <- decompileExpr x.type
--      let indc :=
--        Lean.mkInductiveValEx x.name x.levelParams type x.numParams x.numIndices
--          x.all (x.ctors.map (·.name)) x.numNested x.isRec false x.isReflexive
--      let ctors <- x.ctors.mapM (decompileCtor x.name)
--      let recrs <- x.recrs.mapM (decompileRecr x.all)
--      return (.inductInfo indc, ctors, recrs)
--  where
--    decompileCtor (indcName: Lean.Name) (x: Ix.Constructor)
--      : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
--      let type <- decompileExpr x.type
--      return .ctorInfo <|
--        Lean.mkConstructorValEx x.name x.levelParams type indcName
--          x.cidx x.numParams x.numFields false
--    decompileRecrRule (x: Ix.RecursorRule) : DecompileM Lean.RecursorRule := do
--      let rhs <- decompileExpr x.rhs
--      return ⟨x.ctor, x.nfields, rhs⟩
--    decompileRecr (indcAll: List Lean.Name) (x: Ix.Recursor)
--      : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
--      let type <- decompileExpr x.type
--      let rules <- x.rules.mapM decompileRecrRule
--      return .recInfo <|
--        Lean.mkRecursorValEx x.name x.levelParams type indcAll
--          x.numParams x.numIndices x.numMotives x.numMinors rules x.k false
--
--partial def decompileConst : Ix.Const -> DecompileM BlockNames
--| .axiom x => withLevels x.levelParams do
--  let ⟨name, c, m⟩ := (<- read).current
--  let type <- decompileExpr x.type
--  let const := (.axiomInfo <| Lean.mkAxiomValEx name x.levelParams type false)
--  insertBlock c m (.single const)
--| .definition x => do
--  let ⟨name, c, m⟩ := (<- read).current
--  let const <- decompileDefn x
--  insertBlock c m (.single const)
--| .inductive x => do
--  let ⟨name, c, m⟩ := (<- read).current
--  let (i, cs, rs) <- decompileIndc x
--  insertBlock c m (.inductive ⟨i, cs, rs⟩)
--| .quotient x => withLevels x.levelParams do
--  let ⟨name, c, m⟩ := (<- read).current
--  let type <- decompileExpr x.type
--  let const := (.quotInfo <| Lean.mkQuotValEx name x.levelParams type x.kind)
--  insertBlock c m (.single const)
--| .inductiveProj x => do
--  let curr@⟨name, c, m⟩ := (<- read).current
--  let bs <- ensureBlock name x.blockCont x.blockMeta
--  match bs with
--  | .inductive ⟨i, _, _⟩ => 
--    if x.idx == 0 && i == name then return bs
--    else throw (.badProjection curr i x.blockCont x.blockMeta "inductive")
--  | .mutualInductive is => match is[x.idx]? with
--    | .some ⟨i, _, _⟩ =>
--       if i == name then return bs
--       else throw (.badProjection curr i x.blockCont x.blockMeta "mutual")
--    | .none => throw (.badProjection curr name x.blockCont x.blockMeta "mutual no idx")
--  | _ => throw (.badProjection curr name x.blockCont x.blockMeta "not inductive")
--| .constructorProj x => do
--  let curr@⟨name, c, m⟩ := (<- read).current
--  let bs <- ensureBlock name.parent x.blockCont x.blockMeta
--  let cs <- match bs with
--    | .inductive ⟨i, cs, _⟩ => 
--      if x.idx == 0 && i == name.parent then pure cs
--      else throw (.badProjection curr i x.blockCont x.blockMeta "inductive")
--    | .mutualInductive is => match is[x.idx]? with
--      | .some ⟨i, cs, _⟩ =>
--         if i == name then pure cs
--         else throw (.badProjection curr i x.blockCont x.blockMeta "mutual")
--      | .none => throw (.badProjection curr name x.blockCont x.blockMeta "mutual no idx")
--    | _ => throw (.badProjection curr name x.blockCont x.blockMeta "not inductive")
--  --match cs[x.cidx]
--  return bs
--| _ => sorry
--
----partial def decompileConst
----  (n: Lean.Name) (c m: Address): Ix.Const -> DecompileM Unit
----| .constructorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, cs, _) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match cs[x.cidx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta s!"bad ctor idx {x.cidx} {cs}"
----    if n == n then return () else 
----      throw <| .badProjection n x.blockCont x.blockMeta "ctor name mismatch"
----| .recursorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, _, rs) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match rs[x.ridx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad recr idx"
----    if n == n then return () else
----      throw <| .badProjection n x.blockCont x.blockMeta "recr name mismatch"
----| .definitionProj x => do
----  ensureMutDefBlock x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.defns ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not defns block"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let n <- match ns[x.idx]? with
----    | .some n => pure n 
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad defn idx"
----    if n == n then return () else throw <| .badProjection n x.blockCont x.blockMeta "defn name mismatch"
------ these should be unreachable here
----| .mutDefBlock x => throw <| .namedMutDefBlock n x
----| .mutIndBlock x => throw <| .namedMutIndBlock n x
----
--
--end
--
----partial def ensureConst'
----  (c m: Address) (n: Option Lean.Name) : DecompileM Unit := do
----  match n, (<- get).blocks.find? (c, m) with
----  | .some name, .some b =>
----    if b.contains name then return ()
----    else throw <| .expectedNameInBlock name b c m
----  | .none, .some b => return ()
----  | n, .none => do
----    let cont : Ixon.Const <- match (<- get).store.find? c with
----      | .some ixon => pure ixon
----      | .none => throw <| .unknownStoreAddress c
----    let meta : Ixon.Metadata <- match (<- get).store.find? m with
----      | .some (.meta meta) => pure meta
----      | .some x => throw <| .expectedIxonMetadata m x
----      | .none => throw <| .unknownStoreAddress m
----    match rematerialize cont meta with
----    | .ok const  => do
----      let consts <- decompileConst' c m n const
----
----    | .error e => throw (.transport e c m)
--
----partial def ensureConst (name: Lean.Name) (cont meta: Address) : DecompileM Unit := do
----  match (<- get).blocks.find? (cont, meta) with
----  | .some (.defn n) => 
----    if n == name then return () else throw <| .mismatchedName name n cont meta
----  | .some x => throw <| .expectedDefnBlock name x cont meta
----  | .none => do
----    let c : Ixon.Const <- match (<- get).store.find? cont with
----      | .some ixon => pure ixon
----      | .none => throw <| .unknownStoreAddress cont
----    let m : Ixon.Metadata <- match (<- get).store.find? meta with
----      | .some (.meta meta) => pure meta
----      | .some x => throw <| .expectedIxonMetadata meta x
----      | .none => throw <| .unknownStoreAddress meta
----    match rematerialize c m with
----    | .ok a  => decompileConst name cont meta a
----    | .error e => throw (.transport e cont meta)
----
----partial def ensureIndBlock (n: Lean.Name) (cont meta: Address) : DecompileM Unit := do
----  match (<- get).blocks.find? (cont, meta) with
----  | .some (.indcs _) => return ()
----  | .some x => throw <| .expectedMutIndBlock x cont meta
----  | .none => do
----    let c : Ixon.Const <- match (<- get).store.find? cont with
----      | .some ixon => pure ixon
----      | .none => throw <| .unknownStoreAddress cont
----    let m : Ixon.Metadata <- match (<- get).store.find? meta with
----      | .some (.meta meta) => pure meta
----      | .some x => throw <| .expectedIxonMetadata meta x
----      | .none => throw <| .unknownStoreAddress meta
----    match rematerialize c m with
----    | .ok (.mutIndBlock x)  => decompileMutIndBlock x cont meta
----    | .ok c@(.«inductive» x) => decompileConst n cont meta c
----    | .ok x => throw <| .expectedMutIndConst x cont meta
----    | .error e => throw (.transport e cont meta)
----
----partial def ensureMutDefBlock (cont meta: Address) : DecompileM Unit := do
----  match (<- get).blocks.find? (cont, meta) with
----  | .some (.defns _) => return ()
----  | .some x => throw <| .expectedMutDefBlock x cont meta
----  | .none => do
----    let c : Ixon.Const <- match (<- get).store.find? cont with
----      | .some ixon => pure ixon
----      | .none => throw <| .unknownStoreAddress cont
----    let m : Ixon.Metadata <- match (<- get).store.find? meta with
----      | .some (.meta meta) => pure meta
----      | .some x => throw <| .expectedIxonMetadata meta x
----      | .none => throw <| .unknownStoreAddress meta
----    match rematerialize c m with
----    | .ok (.mutDefBlock x)  => decompileMutDefBlock x cont meta
----    | .ok x  => throw <| .expectedMutDefConst x cont meta
----    | .error e => throw (.transport e cont meta)
----
----partial def decompileMutDefCtx (ctx: List (List Lean.Name)) 
----  : DecompileM (RBMap Lean.Name Nat compare) := do
----  let mut mutCtx : RBMap Lean.Name Nat compare := RBMap.empty
----  for (ns, i) in List.zipIdx ctx do
----    for n in ns do
----      mutCtx := mutCtx.insert n i
----  return mutCtx
----
----partial def checkCtorRecrLengths : List Ix.Inductive -> DecompileM (Nat × Nat)
----| [] => return (0, 0)
----| x::xs => go x xs
----  where
----    go : Ix.Inductive -> List Ix.Inductive -> DecompileM (Nat × Nat)
----    | x, [] => return (x.ctors.length, x.recrs.length)
----    | x, a::as =>
----      if x.ctors.length == a.ctors.length && x.recrs.length == a.recrs.length
----      then go x as else throw <| .nonCongruentInductives x a
----
----partial def decompileMutIndCtx (block: Ix.MutualInductiveBlock)
----  : DecompileM (RBMap Lean.Name Nat compare) := do
----  let mut mutCtx : RBMap Lean.Name Nat compare := RBMap.empty
----  let mut i := 0
----  for (inds, names) in List.zip block.inds block.ctx do
----    let (numCtors, numRecrs) <- checkCtorRecrLengths inds
----    for (ind, name) in List.zip inds names do
----      mutCtx := mutCtx.insert name i
----      for (c, cidx) in List.zipIdx ind.ctors do
----        mutCtx := mutCtx.insert c.name (i + cidx)
----      for (r, ridx) in List.zipIdx ind.recrs do
----        mutCtx := mutCtx.insert r.name (i + numCtors + ridx)
----    i := i + 1 + numCtors + numRecrs
----  return mutCtx
----
----partial def tryInsertConst
----  (const: Lean.ConstantInfo)
----  : DecompileM Unit := do
----  match (<- get).env.find? const.name with
----  | .some const' =>
----      if const == const'
----      then return ()
----      else throw <| .inconsistentConsts const const'
----  | .none => modify fun stt => { stt with env := stt.env.insert const.name const }
----
----partial def decompileDefn (name: Lean.Name) (c m : Address) (x: Ix.Definition)
----  : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
----    let type <- decompileExpr c m x.type
----    let val <- decompileExpr c m x.value
----    let safety := if x.isPartial then .«partial» else .safe
----    match x.mode with
----    | .definition => return .defnInfo <|
----      Lean.mkDefinitionValEx name x.levelParams type val x.hints safety x.all
----    | .opaque => return .opaqueInfo <|
----      Lean.mkOpaqueValEx name x.levelParams type val true x.all
----    | .theorem => return .thmInfo <|
----      Lean.mkTheoremValEx name x.levelParams type val x.all
----
----partial def decompileIndc 
----  (name: Lean.Name)
----  (c m : Address)
----  (x: Ix.Inductive) :
----  DecompileM 
----    (Lean.ConstantInfo × List Lean.ConstantInfo × List Lean.ConstantInfo)
----    := withLevels x.levelParams do
----      let type <- decompileExpr c m x.type
----      let indc :=
----        Lean.mkInductiveValEx name x.levelParams type x.numParams x.numIndices
----          x.all (x.ctors.map (·.name)) x.numNested x.isRec false x.isReflexive
----      let ctors <- x.ctors.mapM (decompileCtor name)
----      let recrs <- x.recrs.mapM (decompileRecr x.all)
----      return (.inductInfo indc, ctors, recrs)
----  where
----    decompileCtor (indcName: Lean.Name) (x: Ix.Constructor)
----      : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
----      let type <- decompileExpr c m x.type
----      return .ctorInfo <|
----        Lean.mkConstructorValEx x.name x.levelParams type indcName 
----          x.cidx x.numParams x.numFields false
----    decompileRecrRule (x: Ix.RecursorRule) : DecompileM Lean.RecursorRule := do
----      let rhs <- decompileExpr c m x.rhs
----      return ⟨x.ctor, x.nfields, rhs⟩
----    decompileRecr (indcAll: List Lean.Name) (x: Ix.Recursor)
----      : DecompileM Lean.ConstantInfo := withLevels x.levelParams do
----      let type <- decompileExpr c m x.type
----      let rules <- x.rules.mapM decompileRecrRule
----      return .recInfo <|
----        Lean.mkRecursorValEx x.name x.levelParams type indcAll
----          x.numParams x.numIndices x.numMotives x.numMinors rules x.k false
----
----partial def ensureConst'
----  (c m: Address) (n: Option Lean.Name) : DecompileM Unit := do
----  match n, (<- get).blocks.find? (c, m) with
----  | .some name, .some b =>
----    if b.contains name then return ()
----    else throw <| .expectedNameInBlock name b c m
----  | .none, .some b => return ()
----  | n, .none => do
----    let cont : Ixon.Const <- match (<- get).store.find? c with
----      | .some ixon => pure ixon
----      | .none => throw <| .unknownStoreAddress c
----    let meta : Ixon.Metadata <- match (<- get).store.find? m with
----      | .some (.meta meta) => pure meta
----      | .some x => throw <| .expectedIxonMetadata m x
----      | .none => throw <| .unknownStoreAddress m
----    match rematerialize cont meta with
----    | .ok const  => do
----      let consts <- decompileConst' c m n const
----
----    | .error e => throw (.transport e c m)
----
----
----partial def decompileConst' (c m: Address)
----  : Option Lean.Name -> Ix.Const -> DecompileM (List Lean.ConstantInfo)
----| .some n, .«axiom» x => withLevels x.levelParams do
----  let type <- decompileExpr c m x.type
----  return [.axiomInfo <| Lean.mkAxiomValEx n x.levelParams type false]
----| .some n, .«definition» x => do
----  let d <- decompileDefn n c m x
----  return [d]
----| .some n, .«inductive» x => do
----  let (i, _, _) <- decompileIndc n c m x
----  return [i]
----| .some n, .quotient x => withLevels x.levelParams do
----  let type <- decompileExpr c m x.type
----  return [.quotInfo <| Lean.mkQuotValEx n x.levelParams type x.kind]
----| .some n, .inductiveProj x => do
----  ensureConst (.some n) x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some (.indc n) => pure [n]
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indcs or indc block"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (i, _, _) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----    if i == n then return () else throw <| .badProjection n x.blockCont x.blockMeta "indc name mismatch"
----| .constructorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, cs, _) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match cs[x.cidx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta s!"bad ctor idx {x.cidx} {cs}"
----    if n == n then return () else 
----      throw <| .badProjection n x.blockCont x.blockMeta "ctor name mismatch"
----| .recursorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, _, rs) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match rs[x.ridx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad recr idx"
----    if n == n then return () else
----      throw <| .badProjection n x.blockCont x.blockMeta "recr name mismatch"
----| .definitionProj x => do
----  ensureMutDefBlock x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.defns ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not defns block"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let n <- match ns[x.idx]? with
----    | .some n => pure n 
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad defn idx"
----    if n == n then return () else throw <| .badProjection n x.blockCont x.blockMeta "defn name mismatch"
----| .none, .mutDefBlock x => sorry
----| .none, .mutIndBlock x => sorry
----
----
----partial def decompileConst
----  (n: Lean.Name) (c m: Address): Ix.Const -> DecompileM Unit
----| .axiom x => withLevels x.levelParams do
----  let type <- decompileExpr c m x.type
----  let val := Lean.mkAxiomValEx n x.levelParams type false
----  tryInsertConst (.axiomInfo val)
----| .definition x => do
----  decompileDefn n c m x >>= tryInsertConst
----  modify fun stt => 
----    { stt with blocks := stt.blocks.insert (c, m) (.defn i) }
----| .inductive x => do
----  let (i, cs, rs) <- decompileIndc n c m x
----  tryInsertConst i
----  let cns <- cs.mapM <| fun c => tryInsertConst c *> pure c.name
----  let rns <- rs.mapM <| fun r => tryInsertConst r *> pure r.name
----  modify fun stt => 
----    { stt with blocks := stt.blocks.insert (c, m) (.indcs [(i.name, cns, rns)]) }
----| .quotient x => withLevels x.levelParams do
----  let type <- decompileExpr c m x.type
----  let val :=  Lean.mkQuotValEx n x.levelParams type x.kind
----  tryInsertConst (.quotInfo val)
----| .inductiveProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indcs block"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (i, _, _) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----    if i == n then return () else throw <| .badProjection n x.blockCont x.blockMeta "indc name mismatch"
----| .constructorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, cs, _) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match cs[x.cidx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta s!"bad ctor idx {x.cidx} {cs}"
----    if n == n then return () else 
----      throw <| .badProjection n x.blockCont x.blockMeta "ctor name mismatch"
----| .recursorProj x => do
----  ensureIndBlock n x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.indcs ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not indc"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let (_, _, rs) <- match ns[x.idx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad ind idx"
----  let n <- match rs[x.ridx]? with
----    | .some ns => pure ns
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad recr idx"
----    if n == n then return () else
----      throw <| .badProjection n x.blockCont x.blockMeta "recr name mismatch"
----| .definitionProj x => do
----  ensureMutDefBlock x.blockCont x.blockMeta
----  let ns <- match (<- get).blocks.find? (x.blockCont, x.blockMeta) with
----    | .some (.defns ns) => pure ns
----    | .some _ => throw <| .badProjection n x.blockCont x.blockMeta "not defns block"
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "no block"
----  let n <- match ns[x.idx]? with
----    | .some n => pure n 
----    | .none => throw <| .badProjection n x.blockCont x.blockMeta "bad defn idx"
----    if n == n then return () else throw <| .badProjection n x.blockCont x.blockMeta "defn name mismatch"
------ these should be unreachable here
----| .mutDefBlock x => throw <| .namedMutDefBlock n x
----| .mutIndBlock x => throw <| .namedMutIndBlock n x
----
----partial def decompileMutDefBlock
----  (x: Ix.MutualDefinitionBlock)
----  (c m: Address)
----  : DecompileM Unit := do
----  let mutCtx <- decompileMutDefCtx x.ctx
----  withMutCtx mutCtx do
----    let mut block := #[]
----    for (defns, names) in List.zip x.defs x.ctx do
----      for (defn, name) in List.zip defns names do
----        decompileDefn name c m defn >>= tryInsertConst
----        block := block.push name
----    modify fun stt => 
----      { stt with blocks := stt.blocks.insert (c, m) (.defns block.toList) }
----
----partial def decompileMutIndBlock
----  (x: Ix.MutualInductiveBlock)
----  (c m: Address)
----  : DecompileM Unit := do
----  let mutCtx <- decompileMutIndCtx x
----  withMutCtx mutCtx do
----    let mut block := #[]
----    for (inds, names) in List.zip x.inds x.ctx do
----      for (ind, name) in List.zip inds names do
----        let (i, cs, rs) <- decompileIndc name c m ind
----        tryInsertConst i
----        let cs <- cs.mapM <| fun c => tryInsertConst c *> pure c.name
----        let rs <- rs.mapM <| fun r => tryInsertConst r *> pure r.name
----        block := block.push (i.name, cs, rs)
----    modify fun stt =>
----      { stt with blocks := stt.blocks.insert (c, m) (.indcs block.toList)}
----
----end
----
----def decompileEnv : DecompileM Unit := do
----  for (n, (anon, meta)) in (<- get).names do
----    ensureConst n anon meta
--
--end Decompile
