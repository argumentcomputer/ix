import Ix.Address

structure EvalClaim where
  lvls : Address
  input: Address
  output: Address
  type : Address
deriving BEq, Repr, Inhabited

structure CheckClaim where
  lvls : Address
  type : Address
  value : Address
deriving BEq, Repr, Inhabited

inductive Claim where
| evals : EvalClaim -> Claim
| checks : CheckClaim -> Claim
deriving BEq, Repr, Inhabited

instance : ToString CheckClaim where
  toString x := s!"#{x.value} : #{x.type} @ #{x.lvls}"

instance : ToString EvalClaim where
  toString x := s!"#{x.input} ~> #{x.output} : #{x.type} @ #{x.lvls}"

instance : ToString Claim where
  toString
  | .checks x => toString x
  | .evals x => toString x



