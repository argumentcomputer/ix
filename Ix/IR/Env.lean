import Batteries.Data.RBMap
import Ix.IR.Univ
import Ix.IR.Expr
import Ix.IR.Const

namespace Ix

instance : Ord Lean.Name where
  compare := Lean.Name.quickCmp

structure Env where
  consts : Batteries.RBMap Lean.Name Address compare
  blocks : Batteries.RBSet Address compare
