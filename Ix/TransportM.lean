import Ix.IR.Univ
import Ix.Ixon.Univ
import Ix.IR.Expr
import Ix.Ixon.Expr
import Ix.IR.Const
import Ix.Ixon.Const
import Ix.Common
import Ix.Address
import Ix.Ixon.Metadata
import Ix.Ixon.Serialize
import Ix.Prove
import Batteries.Data.RBMap

namespace Ix.TransportM

structure DematState where
  idx: Nat
  meta: Ixon.Metadata
  deriving Repr

def emptyDematState : DematState := 
  { idx := 0, meta := { map := Batteries.RBMap.empty }}

inductive TransportError
  | natTooBig (idx: Nat) (x: Nat)
  | unknownIndex (idx: Nat) (m: Ixon.Metadata)
  | unexpectedNode (idx: Nat) (m: Ixon.Metadata)
  | rawMetadata (m: Ixon.Metadata)
  | rawProof (m: Proof)
  deriving Repr

abbrev DematM := EStateM TransportError DematState

structure RematState where
  idx: Nat

def emptyRematState : RematState := { idx := 0 }

structure RematCtx where
  meta: Ixon.Metadata

abbrev RematM := ReaderT RematCtx (EStateM TransportError RematState)

def countSucc : Ix.Univ -> Nat -> (Nat × Ix.Univ)
| .succ x, i => countSucc x (.succ i)
| n, i => (i, n)

def unrollSucc : Nat -> Ix.Univ -> Ix.Univ
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

def dematMeta (node: Ixon.MetaNode): DematM Unit := do
  let n <- (·.idx) <$> get
  modify fun stt =>
    { stt with meta :=
      { stt.meta with map := stt.meta.map.insert n node } }

partial def dematUniv : Ix.Univ -> DematM Ixon.Univ
| .zero => dematIncr *> return .const 0
| .succ x => match countSucc x 1 with
  | (i, .zero) => dematIncrN (i + 1) *> .const <$> dematNat i
  | (i, x) => dematIncrN (i + 1) *> .add <$> dematNat i <*> dematUniv x
| .max x y => dematIncr *> .max <$> dematUniv x <*> dematUniv y
| .imax x y => dematIncr *> .imax <$> dematUniv x <*> dematUniv y
| .var n i => do
  let _ <- dematIncr
  dematMeta { name := .some n, info := .none, link := .none }
  .var <$> dematNat i

def rematIncrN (x: Nat) : RematM Nat := do
  let n <- (·.idx) <$> get
  modify fun stt => { stt with idx := n + x }
  return n + x

def rematIncr : RematM Nat := rematIncrN 1

def rematMeta : RematM Ixon.MetaNode := do
  let n <- (·.idx) <$> get
  let m <- (·.meta) <$> read
  match m.map.find? n with
  | .some n => return n
  | .none => throw (.unknownIndex n m)

def rematThrowUnexpectedNode : RematM α := do
  let n <- (·.idx) <$> get
  let m <- (·.meta) <$> read
  throw (.unexpectedNode n m)

def rematBindMeta : RematM (Lean.Name × Lean.BinderInfo) := do
  let n <- rematMeta
  match n.name, n.info with
  | .some n, some i => return (n, i)
  | _, _ => rematThrowUnexpectedNode

def rematUniv : Ixon.Univ -> RematM Ix.Univ
| .const i => do
  let i' := UInt64.toNat i
  rematIncrN (i' + 1) *> return (unrollSucc i') .zero
| .add i x => do
  let i' := UInt64.toNat i
  rematIncrN (i' + 1) *> (unrollSucc i') <$> rematUniv x
| .max x y => rematIncr *> .max <$> rematUniv x <*> rematUniv y
| .imax x y => rematIncr *> .imax <$> rematUniv x <*> rematUniv y
| .var x => do
  let k <- rematIncr
  let mn <- rematMeta
  match mn.name with
  | .some name => return .var name (UInt64.toNat x)
  | .none => read >>= fun ctx => throw (.unexpectedNode k ctx.meta)

partial def dematExpr : Ix.Expr -> DematM Ixon.Expr
| .var i => dematIncr *> .vari <$> dematNat i
| .sort u => dematIncr *> .sort <$> dematUniv u
| .const n r m us => do
  let _ <- dematIncr
  dematMeta { name := .some n, info := .none, link := .some m }
  .cnst r <$> (us.mapM dematUniv)
| .rec_ i us => dematIncr *> .rec_ <$> dematNat i <*> (us.mapM dematUniv)
| .app f a => apps f a []
| .lam n i t b => lams (.lam n i t b) []
| .pi n i t b => alls (.pi n i t b) []
| .letE n t v b nD => do
  let _ <- dematIncr
  dematMeta { name := .some n, info := .none, link := none }
  .let_ nD <$> dematExpr t <*> dematExpr v <*> dematExpr b
| .lit l => dematIncr *> match l with
  | .strVal s => return .strl s
  | .natVal n => return .natl n
| .proj n t tM i s => do
  let _ <- dematIncr
  dematMeta { name := .some n, info := .none, link := .some tM }
  .proj t <$> dematNat i <*> dematExpr s
  where
    apps : Ix.Expr -> Ix.Expr -> List Ix.Expr -> DematM Ixon.Expr
    | .app ff fa, a, as => apps ff fa (a::as)
    | f, a, as => do
      let as' <- as.reverse.mapM (fun a => dematIncr *> dematExpr a)
      .apps <$> dematExpr f <*> dematExpr a <*> pure (as'.reverse)
    lams : Ix.Expr -> List Ixon.Expr -> DematM Ixon.Expr
    | .lam n i t b, ts => do
      let _ <- dematIncr
      dematMeta { name := .some n, info := .some i, link := .none}
      let t' <- dematExpr t
      lams b (t'::ts)
    | x, ts => .lams ts.reverse <$> dematExpr x
    alls : Ix.Expr -> List Ixon.Expr -> DematM Ixon.Expr
    | .pi n i t b, ts => do
      let _ <- dematIncr
      dematMeta { name := .some n, info := .some i, link := .none}
      let t' <- dematExpr t
      alls b (t'::ts)
    | x, ts => .alls ts.reverse <$> dematExpr x

partial def rematExpr : Ixon.Expr -> RematM Ix.Expr
| .vari i => rematIncr *> pure (.var i.toNat)
| .sort u => rematIncr *> .sort <$> rematUniv u
| .cnst adr us => do
  let _ <- rematIncr
  let node <- rematMeta
  let us' <- us.mapM rematUniv
  match node.name, node.link with
  | .some name, .some link => return (.const name adr link us')
  | _, _ => rematThrowUnexpectedNode
| .rec_ i us => rematIncr *> .rec_ i.toNat <$> us.mapM rematUniv
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
| .let_ nD t d b => do
  let _ <- rematIncr
  let m <- (·.name) <$> rematMeta
  let name <- match m with
    | .some m => pure m
    | _ => rematThrowUnexpectedNode
  .letE name <$> rematExpr t <*> rematExpr d <*> rematExpr b <*> pure nD
| .proj t i s => do
  let _ <- rematIncr
  let m <- rematMeta
  let (name, link) <- match m.name, m.link with
    | .some n, .some l => pure (n, l)
    | _, _ => rematThrowUnexpectedNode
  .proj name t link i.toNat <$> rematExpr s
| .strl s => rematIncr *> return .lit (.strVal s)
| .natl n => rematIncr *> return .lit (.natVal n)

partial def dematConst : Ix.Const -> DematM Ixon.Const
| .«axiom» x => .axio <$> (.mk x.lvls <$> dematExpr x.type)
| .«theorem» x => .theo <$> (.mk x.lvls <$> dematExpr x.type <*> dematExpr x.value)
| .«opaque» x => 
  .opaq <$> (.mk x.lvls <$> dematExpr x.type <*> dematExpr x.value)
| .«definition» x => .defn <$> dematDefn x
| .quotient x => .quot <$> 
  (.mk x.lvls <$> dematExpr x.type <*> pure x.kind)
| .inductiveProj x => do
  dematMeta { name := .none, info := .none, link := .some x.blockMeta}
  return .indcProj (.mk x.blockCont x.idx)
| .constructorProj x => do
  dematMeta { name := .none, info := .none, link := .some x.blockMeta}
  return .ctorProj (.mk x.blockCont x.idx x.cidx)
| .recursorProj x => do
  dematMeta { name := .none, info := .none, link := .some x.blockMeta}
  return .recrProj (.mk x.blockCont x.idx x.ridx)
| .definitionProj x => do
  dematMeta { name := .none, info := .none, link := .some x.blockMeta}
  return .defnProj (.mk x.blockCont x.idx)
| .mutDefBlock xs => .mutDef <$> (xs.mapM dematDefn)
| .mutIndBlock xs => .mutInd <$> (xs.mapM dematInd)
  where
    dematDefn : Ix.Definition -> DematM Ixon.Definition
    | x => .mk x.lvls <$> dematExpr x.type <*> dematExpr x.value <*> pure x.part
    dematCtor : Ix.Constructor -> DematM Ixon.Constructor
    | x => do
      let t <- dematExpr x.type
      return .mk x.lvls t x.idx x.params x.fields
    dematRecr : Ix.Recursor -> DematM Ixon.Recursor
    | x => do
      let t <- dematExpr x.type
      let rrs <- x.rules.mapM (fun rr => .mk rr.fields <$> dematExpr rr.rhs)
      return .mk x.lvls t x.params x.indices x.motives x.minors rrs x.isK x.internal
    dematInd : Ix.Inductive -> DematM Ixon.Inductive
    | x => do
      let t <- dematExpr x.type
      let cs <- x.ctors.mapM dematCtor
      let rs <- x.recrs.mapM dematRecr
      return .mk x.lvls t x.params x.indices cs rs x.recr x.refl x.struct x.unit

def constToIxon (x: Ix.Const) : Except TransportError (Ixon.Const × Ixon.Const) := 
  match EStateM.run (dematConst x) emptyDematState with
  | .ok ix stt => .ok (ix, Ixon.Const.meta stt.meta)
  | .error e _ => .error e

def constToBytes (x: Ix.Const) : Except TransportError ByteArray := do
  let (ix, _) <- constToIxon x
  return Ixon.Serialize.put ix

def constAddress (x: Ix.Const) : Except TransportError Address := do
  let bs <- constToBytes x
  return Address.blake3 bs

partial def rematConst : Ixon.Const -> RematM Ix.Const
| .axio x => .«axiom» <$> (.mk x.lvls <$> rematExpr x.type)
| .theo x => .«theorem» <$> (.mk x.lvls <$> rematExpr x.type <*> rematExpr x.value)
| .opaq x => .«opaque» <$> (.mk x.lvls <$> rematExpr x.type <*> rematExpr x.value)
| .defn x => .«definition» <$> rematDefn x
| .quot x => .quotient <$> (.mk x.lvls <$> rematExpr x.type <*> pure x.kind)
| .indcProj x => do
  let link <- rematMeta >>= fun m => m.link.elim rematThrowUnexpectedNode pure
  return .inductiveProj (.mk x.block link x.idx)
| .ctorProj x => do
  let link <- rematMeta >>= fun m => m.link.elim rematThrowUnexpectedNode pure
  return .constructorProj (.mk x.block link x.idx x.cidx)
| .recrProj x => do
  let link <- rematMeta >>= fun m => m.link.elim rematThrowUnexpectedNode pure
  return .recursorProj (.mk x.block link x.idx x.ridx)
| .defnProj x => do
  let link <- rematMeta >>= fun m => m.link.elim rematThrowUnexpectedNode pure
  return .definitionProj (.mk x.block link x.idx)
| .mutDef xs => .mutDefBlock <$> (xs.mapM rematDefn)
| .mutInd xs => .mutIndBlock <$> (xs.mapM rematInd)
| .meta m => throw (.rawMetadata m)
| .proof p => throw (.rawProof p)
  where
    rematDefn : Ixon.Definition -> RematM Ix.Definition
    | x => .mk x.lvls <$> rematExpr x.type <*> rematExpr x.value <*> pure x.part
    rematCtor : Ixon.Constructor -> RematM Ix.Constructor
    | x => do
      let t <- rematExpr x.type
      return .mk x.lvls t x.idx x.params x.fields
    rematRecr : Ixon.Recursor -> RematM Ix.Recursor
    | x => do
      let t <- rematExpr x.type
      let rrs <- x.rules.mapM (fun rr => .mk rr.fields <$> rematExpr rr.rhs)
      return .mk x.lvls t x.params x.indices x.motives x.minors rrs x.isK x.internal
    rematInd : Ixon.Inductive -> RematM Ix.Inductive
    | x => do
      let t <- rematExpr x.type
      let cs <- x.ctors.mapM rematCtor
      let rs <- x.recrs.mapM rematRecr
      return .mk x.lvls t x.params x.indices cs rs x.recr x.refl x.struct x.unit

end Ix.TransportM
