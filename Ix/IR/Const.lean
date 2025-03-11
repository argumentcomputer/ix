import Ix.IR.Univ
import Ix.IR.Expr
import Ix.Address

deriving instance BEq, Repr, Hashable, Ord for Lean.QuotKind

namespace Ix

structure Quotient where
  lvls : Nat
  type : Expr
  kind : Lean.QuotKind
  deriving Ord, BEq, Hashable, Repr

structure Axiom where
  lvls  : Nat
  type  : Expr
  deriving Ord, BEq, Hashable, Repr

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving Ord, BEq, Hashable, Repr

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving BEq, Ord, Hashable, Repr

structure Definition where
  lvls  : Nat
  type  : Expr
  value : Expr
  part  : Bool
  deriving BEq, Ord, Hashable, Repr

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  deriving BEq, Ord, Hashable, Repr

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving BEq, Ord, Hashable, Repr

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
  deriving BEq, Ord, Hashable, Repr

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
  deriving BEq, Ord, Hashable, Repr

structure InductiveProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  deriving BEq, Ord, Hashable, Repr

structure ConstructorProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  cidx  : Nat
  deriving BEq, Ord, Hashable, Repr

structure RecursorProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  ridx  : Nat
  deriving BEq, Ord, Hashable, Repr

structure DefinitionProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  deriving BEq, Ord, Hashable, Repr

inductive Const where
  | «axiom»     : Axiom      → Const
  | «theorem»   : Theorem    → Const
  | «opaque»    : Opaque     → Const
  | «definition»: Definition → Const
  | quotient    : Quotient   → Const
  -- projections of mutual blocks
  | inductiveProj   : InductiveProj   → Const
  | constructorProj : ConstructorProj → Const
  | recursorProj    : RecursorProj    → Const
  | definitionProj  : DefinitionProj  → Const
  -- constants to represent mutual blocks
  | mutDefBlock : List Definition → Const
  | mutIndBlock : List Inductive  → Const
  deriving Ord, BEq, Inhabited, Repr

def Const.isMutType : Const → Bool
  | .mutDefBlock _ | .mutIndBlock _ => true
  | _ => false

end Ix
