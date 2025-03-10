import Ix.IR.Univ
import Ix.Address
import Ix.Common
import Lean.Expr

namespace Ix

inductive Expr
  | var   (idx: Nat)
  | sort  (univ: Univ)
  | const (name: Lean.Name) (ref: Address) (meta: Address) (univs: List Univ)
  | rec_  (idx: Nat) (univs: List Univ)
  | app   (func: Expr) (argm: Expr)
  | lam   (name: Lean.Name) (info: Lean.BinderInfo) (type: Expr) (body: Expr)
  | pi    (name: Lean.Name) (info: Lean.BinderInfo) (type: Expr) (body: Expr)
  | letE  (name: Lean.Name) (type: Expr) (value: Expr) (body: Expr) (nonDep: Bool)
  | lit   (lit: Lean.Literal)
  | proj  (typeName: Lean.Name) (typeCont: Address) (typeMeta: Address) (idx: Nat) (struct: Expr)
  deriving Inhabited, Ord, BEq, Repr, Hashable

end Ix
