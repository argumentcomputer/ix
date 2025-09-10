import Ix.IR
import Ix.Ixon.Univ
import Ix.Ixon
import Ix.Common
import Ix.Address
import Ix.Ixon.Metadata
import Ix.Ixon.Serialize
import Ix.Prove
import Batteries.Data.RBMap

namespace Ix.TransportM

open Ixon

structure DematState where
  idx: Nat
  store: Batteries.RBMap Address Ixon compare
  meta: Ixon.Metadata
  deriving Repr

def emptyDematState : DematState := 
  { idx := 0, store := .empty, meta := { map := .empty }}

inductive TransportError
| natTooBig (idx: Nat) (x: Nat)
| unknownIndex (idx: Nat) (m: Ixon.Metadata)
| unknownAddress (adr: Address)
| unexpectedNode (idx: Nat) (m: Ixon.Metadata)
| nonExprIxon (x: Ixon) (m: Ixon.Metadata)
| nonConstIxon (x: Ixon) (m: Ixon.Metadata)
| rawMetadata (m: Ixon.Metadata)
| expectedMetadata (m: Ixon.Ixon)
| rawProof (m: Proof)
| rawComm (m: Ixon.Comm)
| emptyEquivalenceClass
deriving BEq, Repr

instance : ToString TransportError where toString
| .natTooBig idx x => s!"At index {idx}, natural number {x} too big to fit in UInt64"
| .unknownIndex idx x => s!"Unknown index {idx} with metadata {repr x}"
| .unknownAddress x => s!"Unknown address {x}"
| .nonExprIxon x m => s!"Tried to rematerialize {repr x} with metadata {repr m} as expression"
| .nonConstIxon x m => s!"Tried to rematerialize {repr x} with metadata {repr m} as constant"
| .unexpectedNode idx x => s!"Unexpected node at {idx} with metadata {repr x}"
| .rawMetadata x => s!"Can't rematerialize raw metadata {repr x}"
| .expectedMetadata x => s!"Expected metadata, got {repr x}"
| .rawProof x => s!"Can't rematerialize raw proof {repr x}"
| .rawComm x => s!"Can't rematerialize raw commitment {repr x}"
| .emptyEquivalenceClass => s!"empty equivalence class, should be unreachable"

abbrev DematM := EStateM TransportError DematState

structure RematState where
  idx: Nat
  store: Batteries.RBMap Address Ixon compare

def emptyRematState : RematState := { idx := 0, store := .empty }

def rematStateWithStore (store: Batteries.RBMap Address Ixon compare) : RematState := 
  { idx := 0, store }

structure RematCtx where
  meta: Ixon.Metadata

abbrev RematM := ReaderT RematCtx (EStateM TransportError RematState)

def countSucc : Ix.Level -> Nat -> (Nat × Ix.Level)
| .succ x, i => countSucc x (.succ i)
| n, i => (i, n)

def unrollSucc : Nat -> Ix.Level -> Ix.Level
| 0, x => x
| .succ i, x => unrollSucc i (.succ x)

def dematNat (x: Nat): DematM UInt64 :=
  if x > UInt64.MAX.toNat then
    get >>= fun stt => throw (.natTooBig stt.idx x)
    else return x.toUInt64

def dematIncrN (x: Nat) : DematM Nat := do
  let n <- (·.idx) <$> get
  modify fun stt => { stt with idx := n + x }
  return n + x

def dematIncr : DematM Nat := dematIncrN 1

def dematMeta (node: List Ixon.Metadatum): DematM Unit := do
  let n <- (·.idx) <$> get
  modify fun stt =>
    { stt with meta :=
      { stt.meta with map := stt.meta.map.insert n node } }

partial def dematUniv : Ix.Level -> DematM Ixon.Univ
| .zero => dematIncr *> return .const 0
| .succ x => match countSucc x 1 with
  | (i, .zero) => dematIncrN (i + 1) *> .const <$> dematNat i
  | (i, x) => dematIncrN (i + 1) *> .add <$> dematNat i <*> dematUniv x
| .max x y => dematIncr *> .max <$> dematUniv x <*> dematUniv y
| .imax x y => dematIncr *> .imax <$> dematUniv x <*> dematUniv y
| .param n i => do
  let _ <- dematIncr
  dematMeta [.name n]
  .var <$> dematNat i

partial def dematLevels (lvls: List Lean.Name): DematM Nat :=
  go 0 lvls
  where
    go (acc: Nat) : List Lean.Name -> DematM Nat
    | n::ns => do
      let _ <- dematIncr
      dematMeta [.name n]
      go (acc+1) ns
    | [] => pure acc

def rematIncrN (x: Nat) : RematM Nat := do
  let n <- (·.idx) <$> get
  modify fun stt => { stt with idx := n + x }
  return n + x

def rematIncr : RematM Nat := rematIncrN 1

def rematMeta : RematM (List Ixon.Metadatum) := do
  let n <- (·.idx) <$> get
  let m <- (·.meta) <$> read
  match m.map.find? n with
  | .some n => return n
  | .none => throw (.unknownIndex n m)

def rematThrowUnexpected : RematM α := do
  let n <- (·.idx) <$> get
  let m <- (·.meta) <$> read
  throw (.unexpectedNode n m)

partial def rematLevels (lvls: Nat): RematM (List Lean.Name) := do
  go [] lvls
  where
    go (acc: List Lean.Name): Nat -> RematM (List Lean.Name)
    | 0 => pure acc.reverse
    | i => do
      let _ <- rematIncr
      match (<- rematMeta) with
      | [.name n] => go (n::acc) (i - 1)
      | _ => rematThrowUnexpected

def rematBindMeta : RematM (Lean.Name × Lean.BinderInfo) := do
  match (<- rematMeta) with
  | [.name n, .info i] => return (n, i)
  | _ => rematThrowUnexpected

def rematUniv : Ixon.Univ -> RematM Ix.Level
| .const i => do
  let i' := UInt64.toNat i
  rematIncrN (i' + 1) *> return (unrollSucc i') .zero
| .add i x => do
  let i' := UInt64.toNat i
  rematIncrN (i' + 1) *> (unrollSucc i') <$> rematUniv x
| .max x y => rematIncr *> .max <$> rematUniv x <*> rematUniv y
| .imax x y => rematIncr *> .imax <$> rematUniv x <*> rematUniv y
| .var x => do
  let _ <- rematIncr
  match (<- rematMeta) with
  | [.name name] => return .param name (UInt64.toNat x)
  | _ => rematThrowUnexpected

partial def dematExpr : Ix.Expr -> DematM Ixon
| .var i => dematIncr *> .vari <$> dematNat i
| .sort u => dematIncr *> .sort <$> dematUniv u
| .const n r m us => do
  let _ <- dematIncr
  dematMeta [.name n, .link m ]
  .refr r <$> (us.mapM dematUniv)
| .rec_ n i us => do
  let _ <- dematIncr
  dematMeta [.name n]
  .recr <$> dematNat i <*> (us.mapM dematUniv)
| .app f a => apps f a []
| .lam n i t b => lams (.lam n i t b) []
| .pi n i t b => alls (.pi n i t b) []
| .letE n t v b nD => do
  let _ <- dematIncr
  dematMeta [.name n]
  .letE nD <$> dematExpr t <*> dematExpr v <*> dematExpr b
| .lit l => dematIncr *> match l with
  | .strVal s => return .strl s
  | .natVal n => return .natl n
| .proj n t tM i s => do
  let _ <- dematIncr
  dematMeta [.name n, .link tM ]
  .proj t <$> dematNat i <*> dematExpr s
  where
    apps : Ix.Expr -> Ix.Expr -> List Ix.Expr -> DematM Ixon
    | .app ff fa, a, as => apps ff fa (a::as)
    | f, a, as => do
      let as' <- as.reverse.mapM (fun a => dematIncr *> dematExpr a)
      .apps <$> dematExpr f <*> dematExpr a <*> pure (as'.reverse)
    lams : Ix.Expr -> List Ixon -> DematM Ixon
    | .lam n i t b, ts => do
      let _ <- dematIncr
      dematMeta [.name n, .info i]
      let t' <- dematExpr t
      lams b (t'::ts)
    | x, ts => .lams ts.reverse <$> dematExpr x
    alls : Ix.Expr -> List Ixon -> DematM Ixon
    | .pi n i t b, ts => do
      let _ <- dematIncr
      dematMeta [.name n, .info i]
      let t' <- dematExpr t
      alls b (t'::ts)
    | x, ts => .alls ts.reverse <$> dematExpr x

partial def rematExpr : Ixon -> RematM Ix.Expr
| .vari i => rematIncr *> pure (.var i.toNat)
| .sort u => rematIncr *> .sort <$> rematUniv u
| .refr adr us => do
  let _ <- rematIncr
  let node <- rematMeta
  let us' <- us.mapM rematUniv
  match node with
  | [.name name, .link link] => return (.const name adr link us')
  | _ => rematThrowUnexpected
| .recr i us => do 
  let _ <- rematIncr
  let node <- rematMeta
  let us' <- us.mapM rematUniv
  match node with
  | [.name name] => return (.rec_ name i.toNat us')
  | _ => rematThrowUnexpected
| .apps f a as => do
  let as' <- as.reverse.mapM (fun e => rematIncr *> rematExpr e)
  let f' <- rematExpr f
  let a' <- rematExpr a
  return as'.reverse.foldl .app (.app f' a')
| .lams ts b => do
  let ts' <- ts.mapM 
    (fun e => rematIncr *> Prod.mk <$> rematBindMeta <*> rematExpr e)
  let b' <- rematExpr b
  return ts'.foldr (fun (m, t) b => Expr.lam m.fst m.snd t b) b'
| .alls ts b => do
  let ts' <- ts.mapM
    (fun e => rematIncr *> Prod.mk <$> rematBindMeta <*> rematExpr e)
  let b' <- rematExpr b
  return ts'.foldr (fun (m, t) b => Expr.pi m.fst m.snd t b) b'
| .letE nD t d b => do
  let _ <- rematIncr
  let node <- rematMeta
  let name <- match node with
    | [.name n] => pure n
    | _ => rematThrowUnexpected
  .letE name <$> rematExpr t <*> rematExpr d <*> rematExpr b <*> pure nD
| .proj t i s => do
  let _ <- rematIncr
  let node <- rematMeta
  let (name, link) <- match node with
    | [.name n, .link l] => pure (n, l)
    | _ => rematThrowUnexpected
  .proj name t link i.toNat <$> rematExpr s
| .strl s => rematIncr *> return .lit (.strVal s)
| .natl n => rematIncr *> return .lit (.natVal n)
| e => do throw (.nonExprIxon e (<- read).meta)

def dematStore (ixon: Ixon): DematM Address :=
  let addr := Address.blake3 (Ixon.runPut (Ixon.Serialize.put ixon))
  modifyGet fun stt => (addr, { stt with
    store := stt.store.insert addr ixon
  })

partial def dematConst : Ix.Const -> DematM Ixon
| .«axiom» x => do
  dematMeta [.name x.name]
  let lvls <- dematLevels x.levelParams
  let type <- dematExpr x.type >>= dematStore
  return .axio (.mk lvls type x.isUnsafe)
| .«definition» x => .defn <$> dematDefn x
| .quotient x => do
  dematMeta [.name x.name]
  let lvls <- dematLevels x.levelParams
  let type <- dematExpr x.type >>= dematStore
  return .quot (.mk lvls type x.kind)
| .inductiveProj x => do
  dematMeta [.name x.name, .link x.blockMeta]
  return .iprj (.mk x.blockCont x.idx)
| .constructorProj x => do
  dematMeta [.name x.name, .link x.blockMeta, .name x.induct]
  return .cprj (.mk x.blockCont x.idx x.cidx)
| .recursorProj x => do
  dematMeta [.name x.name, .link x.blockMeta, .name x.induct]
  return .rprj (.mk x.blockCont x.idx x.ridx)
| .definitionProj x => do
  dematMeta [.name x.name, .link x.blockMeta]
  return .dprj (.mk x.blockCont x.idx)
| .mutual x => do
  dematMeta [.mutCtx x.ctx]
  let defs <- x.defs.mapM fun ds => ds.mapM dematDefn
  let ds <- defs.mapM fun d => match d.head? with
    | .some a => pure a
    | .none => throw .emptyEquivalenceClass
  return .defs ds
| .inductive x => do
  dematMeta [.mutCtx x.ctx]
  let inds <- x.inds.mapM fun is => is.mapM dematIndc
  let is <- inds.mapM fun i => match i.head? with
    | .some a => pure a
    | .none => throw .emptyEquivalenceClass
  return .inds is
  where
    dematDefn (x: Ix.Definition): DematM Ixon.Definition := do
      let _ <- dematIncr
      dematMeta [.name x.name, .hints x.hints, .all x.all]
      let lvls <- dematLevels x.levelParams
      let type <- dematExpr x.type >>= dematStore
      let value <- dematExpr x.value >>= dematStore
      return .mk lvls type x.mode value x.safety
    dematCtor (x: Ix.Constructor): DematM Ixon.Constructor := do
      let _ <- dematIncr
      dematMeta [.name x.name]
      let lvls <- dematLevels x.levelParams
      let t <- dematExpr x.type >>= dematStore
      return .mk lvls t x.cidx x.numParams x.numFields x.isUnsafe
    dematRecrRule (x: Ix.RecursorRule): DematM Ixon.RecursorRule := do
      let _ <- dematIncr
      dematMeta [.name x.ctor]
      let rhs <- dematExpr x.rhs >>= dematStore
      return ⟨x.nfields, rhs⟩
    dematRecr (x: Ix.Recursor): DematM Ixon.Recursor := do
      let _ <- dematIncr
      dematMeta [.name x.name]
      let lvls <- dematLevels x.levelParams
      let t <- dematExpr x.type >>= dematStore
      let rrs <- x.rules.mapM dematRecrRule
      return ⟨lvls, t, x.numParams, x.numIndices, x.numMotives, x.numMinors, 
        rrs, x.k, x.isUnsafe⟩
    dematIndc (x: Ix.Inductive): DematM Ixon.Inductive := do
      let _ <- dematIncr
      dematMeta [.name x.name, .all x.all]
      let lvls <- dematLevels x.levelParams
      let type <- dematExpr x.type >>= dematStore
      let ctors <- x.ctors.mapM dematCtor
      let recrs <- x.recrs.mapM dematRecr
      return ⟨lvls, type, x.numParams, x.numIndices, ctors, recrs, x.numNested,
        x.isRec, x.isReflexive, x.isUnsafe⟩

def constToIxon (x: Ix.Const) : Except TransportError (Ixon × Ixon) := 
  match EStateM.run (dematConst x) emptyDematState with
  | .ok ix stt => .ok (ix, Ixon.meta stt.meta)
  | .error e _ => .error e

def constToBytes (x: Ix.Const) : Except TransportError ByteArray := do
  let (ix, _) <- constToIxon x
  return runPut (Serialize.put ix)

def constAddress (x: Ix.Const) : Except TransportError Address := do
  let bs <- constToBytes x
  return Address.blake3 bs

def rematAddress (adr: Address): RematM Ixon := do
  match (<- get).store.find? adr with
  | .some x => return x
  | .none => throw (.unknownAddress adr)

def rematExprAddress (adr: Address): RematM Ix.Expr := do
  match (<- get).store.find? adr with
  | .some x => rematExpr x
  | .none => throw (.unknownAddress adr)

partial def rematConst : Ixon -> RematM Ix.Const
| .defn x => .«definition» <$> rematDefn x
| .axio x => do
  let name <- match (<- rematMeta) with
    | [.name x] => pure x
    | _ => rematThrowUnexpected
  let lvls <- rematLevels x.lvls
  let type <- rematExprAddress x.type
  return .«axiom» ⟨name, lvls, type, x.isUnsafe⟩
| .quot x => do
  let name <- match (<- rematMeta) with
    | [.name x] => pure x
    | _ => rematThrowUnexpected
  let lvls <- rematLevels x.lvls
  let type <- rematExprAddress x.type
  return .quotient ⟨name, lvls, type, x.kind⟩
| .iprj x => do
  let (name, link) <- match (<- rematMeta) with
    | [.name n, .link x] => pure (n, x)
    | _ => rematThrowUnexpected
  return .inductiveProj ⟨name, x.block, link, x.idx⟩
| .cprj x => do
  let (name, link, induct) <- match (<- rematMeta) with
    | [.name n, .link x, .name i] => pure (n, x, i)
    | _ => rematThrowUnexpected
  return .constructorProj ⟨name, x.block, link, x.idx, induct, x.cidx⟩
| .rprj x => do
  let (name, link, induct) <- match (<- rematMeta) with
    | [.name n, .link x, .name i] => pure (n, x, i)
    | _ => rematThrowUnexpected
  return .recursorProj ⟨name, x.block, link, x.idx, induct, x.ridx⟩
| .dprj x => do
  let (name, link) <- match (<- rematMeta) with
    | [.name n, .link x] => pure (n, x)
    | _ => rematThrowUnexpected
  return .definitionProj ⟨name, x.block, link, x.idx⟩
| .defs xs => do
  let ctx <- match (<- rematMeta) with
    | [.mutCtx x] => pure x
    | _ => rematThrowUnexpected
  let mut defs := #[]
  for (x, ns) in List.zip xs ctx do
    let mut ds := #[]
    for _ in ns do
      let d <- rematDefn x
      ds := ds.push d
    defs := defs.push ds.toList
  return .mutual ⟨defs.toList⟩
| .inds xs => do
  let ctx <- match (<- rematMeta) with
    | [.mutCtx x] => pure x
    | _ => rematThrowUnexpected
  let mut inds := #[]
  for (x, ns) in List.zip xs ctx do
    let mut is := #[]
    for _ in ns do
      let i <- rematIndc x
      is := is.push i
    inds := inds.push is.toList
  return .inductive ⟨inds.toList⟩
| .meta m => throw (.rawMetadata m)
-- TODO: This could return a Proof inductive, since proofs have no metadata
| .prof p => throw (.rawProof p)
| .comm p => throw (.rawComm p)
| e => do throw (.nonConstIxon e (<- read).meta)
  where
    rematDefn (x: Ixon.Definition) : RematM Ix.Definition := do
      let _ <- rematIncr
      let (name, hints, all) <- match (<- rematMeta) with
        | [.name n, .hints h, .all as] => pure (n, h, as)
        | _ => rematThrowUnexpected
      let lvls <- rematLevels x.lvls
      let type <- rematExprAddress x.type
      let value <- rematExprAddress x.value
      return .mk name lvls type x.mode value hints x.safety all
    rematCtor (x: Ixon.Constructor) : RematM Ix.Constructor := do
      let _ <- rematIncr
      let name <- match (<- rematMeta) with
        | [.name n] => pure n
        | _ => rematThrowUnexpected
      let lvls <- rematLevels x.lvls
      let t <- rematExprAddress x.type
      return .mk name lvls t x.cidx x.params x.fields x.isUnsafe
    rematRecrRule (x: Ixon.RecursorRule) : RematM Ix.RecursorRule := do
      let _ <- rematIncr
      let ctor <- match (<- rematMeta) with
        | [.name n] => pure n
        | _ => rematThrowUnexpected
      let rhs <- rematExprAddress x.rhs
      return ⟨ctor, x.fields, rhs⟩
    rematRecr (x: Ixon.Recursor) : RematM Ix.Recursor := do
      let _ <- rematIncr
      let name <- match (<- rematMeta) with
        | [.name n] => pure n
        | _ => rematThrowUnexpected
      let lvls <- rematLevels x.lvls
      let t <- rematExprAddress x.type
      let rs <- x.rules.mapM rematRecrRule
      return ⟨name, lvls, t, x.params, x.indices, x.motives, x.minors, rs, x.k, x.isUnsafe⟩
    rematIndc (x: Ixon.Inductive) : RematM Ix.Inductive := do
      let _ <- rematIncr
      let (name, all) <- match (<- rematMeta) with
        | [.name n, .all as] => pure (n, as)
        | _ => rematThrowUnexpected
      let lvls <- rematLevels x.lvls
      let t <- rematExprAddress x.type
      let cs <- x.ctors.mapM rematCtor
      let rs <- x.recrs.mapM rematRecr
      return ⟨name, lvls, t, x.params, x.indices, all, cs, rs, x.nested, x.recr,
        x.refl, x.isUnsafe⟩

def rematerialize (c m: Ixon) : Except TransportError Ix.Const := do
  let m <- match m with
  | .meta m => pure m
  | x => throw <| .expectedMetadata x
  match ((rematConst c).run { meta := m }).run emptyRematState with
    | .ok a _ => return a
    | .error e _ => throw e

end Ix.TransportM
