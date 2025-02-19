import Ix.IR.Univ
import Ix.Ixon.Univ

namespace Ix.TransportM

structure MetaNode where
  name: Option Lean.Name

structure Metadata where
  metadata : Array MetaNode

inductive TransportError
  | rematBadMetadata (idx: UInt64) (m: Metadata)
  | rematBadMetaNode (x: String)

structure TransportState where
  metadata: Metadata

abbrev TransportM := EStateM TransportError TransportState

def countSucc : Ix.Univ -> Nat -> (Nat × Ix.Univ)
| .succ x, i => countSucc x (.succ i)
| n, i => (i, n)

def unrollSucc : Ix.Univ -> Nat -> Ix.Univ
| x, 0 => x
| x, .succ i => unrollSucc (.succ x) i

-- TODO: Error on UInt64 <-> Nat conversion bounds?
partial def dematUniv : Ix.Univ -> Ixon.Univ
| .zero => .const 0
| .succ x => match countSucc x 1 with
  | (i, .zero) => .const (UInt64.ofNat i)
  | (i, x) => .add (UInt64.ofNat i) (dematUniv x)
| .max x y => .max (dematUniv x) (dematUniv y)
| .imax x y => .imax (dematUniv x) (dematUniv y)
| .var n => .var (UInt64.ofNat n)

partial def rematUniv : Ixon.Univ -> Ix.Univ
| .var x => .var (UInt64.toNat x)
| .const i => unrollSucc .zero (UInt64.toNat i)
| .add i x => unrollSucc (rematUniv x) (UInt64.toNat i)
| .max x y => .max (rematUniv x) (rematUniv y)
| .imax x y => .imax (rematUniv x) (rematUniv y)

-- def dematExpr : Ix.Expr -> TransportM Ixon.Expr
-- def rematExpr
end Ix.TransportM
