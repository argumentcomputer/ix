import Ix.IR.Univ
import Ix.Address
import Lean.Expr

namespace Ix

deriving instance Ord for Lean.Literal

inductive Expr
  /-- Variables are also used to represent recursive calls. When referencing
    constants, the second argument keeps track of the universe levels -/
  | var   : Nat → List Univ → Expr
  | sort  : Univ → Expr
  | const : Address → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Expr → Expr → Expr
  | pi    : Expr → Expr → Expr
  | letE  : Expr → Expr → Expr → Expr
  | lit   : Lean.Literal → Expr
  | proj  : Nat → Expr → Expr
  deriving Inhabited, Ord, BEq, Repr, Hashable

end Ix
