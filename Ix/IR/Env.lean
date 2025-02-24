import Batteries.Data.RBMap
import Ix.IR.Univ
import Ix.IR.Expr
import Ix.IR.Const
import Ix.Common

namespace Ix

structure Env where
  consts : Batteries.RBMap Lean.Name Address compare
  blocks : Batteries.RBSet Address compare
