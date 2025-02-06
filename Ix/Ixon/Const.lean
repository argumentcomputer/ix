import Ix.Address
import Lean.Declaration
import Ix.Ixon.Serialize
import Ix.Ixon.Expr

namespace Ixon

structure Quotient where
  lvls : Nat
  type : Expr
  kind : Lean.QuotKind

structure Axiom where
  lvls  : Nat
  type  : Expr

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr

structure Definition where
  lvls  : Nat
  type  : Expr
  value : Expr
  part  : Bool

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat

structure RecursorRule where
  fields : Nat
  rhs    : Expr

structure Recursor where
  lvls     : Nat
  type     : Expr
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRule
  isK      : Bool
  internal : Bool

structure Inductive where
  lvls    : Nat
  type    : Expr
  params  : Nat
  indices : Nat
  ctors   : List Constructor
  recrs   : List Recursor
  recr    : Bool
  refl    : Bool
  struct  : Bool
  unit    : Bool

structure InductiveProj where
  block : Address
  idx   : Nat

structure ConstructorProj where
  block : Address
  idx   : Nat
  cidx  : Nat

structure RecursorProj where
  block : Address
  idx   : Nat
  ridx  : Nat

structure DefinitionProj where
  block : Address
  idx   : Nat

structure MetaNode where
  name : Option Lean.Name
  link : Option Address

structure Metadata where
  meta: List MetaNode

inductive Const where
  -- 0xC0
  | axio : Axiom -> Const
  -- 0xC1
  | theo : Theorem -> Const
  -- 0xC2
  | opaq : Opaque -> Const
  -- 0xC3
  | defn : Definition -> Const
  -- 0xC4
  | quot : Quotient -> Const
  -- 0xC5
  | ctor : Constructor -> Const
  -- 0xC6
  | recr : Recursor -> Const
  -- 0xC7
  | indc : Inductive -> Const
  -- 0xC8
  | ctorProj : ConstructorProj -> Const
  -- 0xC9
  | recrProj : RecursorProj -> Const
  -- 0xCA
  | indcProj : InductiveProj -> Const
  -- 0xCB
  | defnProj : DefinitionProj -> Const
  -- 0xCC
  | mutDef : List Definition -> Const
  -- 0xCD
  | mutInd : List Inductive -> Const
  -- 0xCE
  | meta   : Metadata -> Const

end Ixon
