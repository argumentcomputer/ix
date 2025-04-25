import Ix.IR.Univ
import Ix.IR.Expr
import Ix.Address

deriving instance BEq, Repr, Hashable, Ord for Lean.QuotKind

namespace Ix

structure Quotient where
  lvls : List Lean.Name
  type : Expr
  kind : Lean.QuotKind
  deriving Ord, BEq, Hashable, Repr, Nonempty

structure Axiom where
  lvls  : List Lean.Name
  type  : Expr
  deriving Ord, BEq, Hashable, Repr, Nonempty

structure Theorem where
  lvls  : List Lean.Name
  type  : Expr
  value : Expr
  deriving Ord, BEq, Hashable, Repr, Nonempty

structure Opaque where
  lvls  : List Lean.Name
  type  : Expr
  value : Expr
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure Definition where
  lvls  : List Lean.Name
  type  : Expr
  value : Expr
  part  : Bool
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure Constructor where
  lvls   : List Lean.Name
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure Recursor where
  lvls     : List Lean.Name
  type     : Expr
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRule
  isK      : Bool
  internal : Bool
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure Inductive where
  lvls    : List Lean.Name
  type    : Expr
  params  : Nat
  indices : Nat
  ctors   : List Constructor
  recrs   : List Recursor
  recr    : Bool
  refl    : Bool
  struct  : Bool
  unit    : Bool
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure InductiveProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure ConstructorProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  cidx  : Nat
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure RecursorProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  ridx  : Nat
  deriving BEq, Ord, Hashable, Repr, Nonempty

structure DefinitionProj where
  blockCont : Address
  blockMeta : Address
  idx   : Nat
  deriving BEq, Ord, Hashable, Repr, Nonempty

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
  deriving Ord, BEq, Inhabited, Repr, Nonempty

def Const.isMutType : Const → Bool
  | .mutDefBlock _ | .mutIndBlock _ => true
  | _ => false

end Ix
