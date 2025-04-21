import Ix.Address

inductive Claim where
| checks (lvls type value: Address) : Claim
| evals (lvls input output type: Address) : Claim
deriving Inhabited, BEq

instance : ToString Claim where
  toString
  | .checks lvls type value => s!"#{value} : #{type} @ #{lvls}"
  | .evals lvls inp out type => s!"#{inp} ~> #{out} : #{type} @ #{lvls}"


