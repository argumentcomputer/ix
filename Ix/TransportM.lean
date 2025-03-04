import Ix.IR.Univ
import Ix.Ixon.Univ
import Ix.IR.Expr
import Ix.Ixon.Expr
import Ix.Common
import Ix.Address
import Ix.Ixon.Metadata
import Batteries.Data.RBMap

namespace Ix.TransportM

structure DematState where
  idx: Nat
  meta: Ixon.Metadata

def emptyDematState : DematState := 
  { idx := 0, meta := { map := Batteries.RBMap.empty }}

inductive TransportError
  | natTooBig (idx: Nat) (x: Nat)
  | unknownIndex (idx: Nat) (m: Ixon.Metadata)
  | unexpectedNode (idx: Nat) (m: Ixon.Metadata)
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
| .app f a => dematIncr *> apps f a []
| .lam n i t b => lams (.lam n i t b) []
| .pi n i t b => alls (.pi n i t b) []
| .letE n t v b nD => do
  let _ <- dematIncr
  dematMeta { name := .some n, info := .none, link := none }
  .let_ nD <$> dematExpr t <*> dematExpr v <*> dematExpr b
| .lit l => dematIncr *> match l with
  | .strVal s => return .strl s
  | .natVal n => return .natl n
| .proj n t i s => do
  let _ <- dematIncr
  dematMeta { .name := .some n, info := .none, link := .some t }
  .proj <$> dematNat i <*> dematExpr s
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
    | x, ts => .lams ts <$> dematExpr x
    alls : Ix.Expr -> List Ixon.Expr -> DematM Ixon.Expr
    | .pi n i t b, ts => do
      let _ <- dematIncr
      dematMeta { name := .some n, info := .some i, link := .none}
      let t' <- dematExpr t
      alls b (t'::ts)
    | x, ts => .alls ts <$> dematExpr x

end Ix.TransportM
