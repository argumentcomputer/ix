import Ix.IR.Univ
import Ix.Ixon.Univ
import Ix.Common

namespace Ix.TransportM

structure MetaNode where
  name: Option Lean.Name
  bind: Option Lean.BinderInfo

structure Metadata where
  metadata : Array MetaNode

structure DematState where
  metadata: Metadata

inductive DematError
  | natTooBig (x: Nat)

abbrev DematM := EStateM DematError DematState

inductive RematError
  | rematBadMetadata (idx: UInt64) (m: Metadata)
  | rematBadMetaNode (x: String)

structure RematState where
  idx: Nat

structure RematCtx where
  metadata: Metadata

abbrev RematM := ReaderT RematCtx (EStateM RematError RematState)

def countSucc : Ix.Univ -> Nat -> (Nat × Ix.Univ)
| .succ x, i => countSucc x (.succ i)
| n, i => (i, n)

def unrollSucc : Nat -> Ix.Univ -> Ix.Univ
| 0, x => x
| .succ i, x => unrollSucc i (.succ x)

def dematNat (x: Nat): DematM UInt64 :=
  if x > UInt64.MAX.toNat then throw (.natTooBig x) else return x.toUInt64

--partial def dematUniv : Ix.Univ -> DematM Ixon.Univ
--| .zero => return .const 0
--| .succ x => match countSucc x 1 with
--  | (i, .zero) => .const <$> dematNat i
--  | (i, x) => .add <$> dematNat i <*> dematUniv x
--| .max x y => .max <$> dematUniv x <*> dematUniv y
--| .imax x y => .imax <$> dematUniv x <*> dematUniv y
--| .var n => .var <$> dematNat n
--
--def rematUniv : Ixon.Univ -> RematM Ix.Univ
--| .var x => return .var (UInt64.toNat x)
--| .const i => return unrollSucc (UInt64.toNat i) .zero
--| .add i x => unrollSucc (UInt64.toNat i) <$> rematUniv x
--| .max x y => .max <$> rematUniv x <*> rematUniv y
--| .imax x y => .imax <$> rematUniv x <*> rematUniv y



end Ix.TransportM
