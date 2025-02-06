import Ix.Address

inductive ProveError
  | mk

abbrev ProveM := ExceptT ProveError IO

structure Proof where
  inp : Address
  out : Address
  typ : Address
  bin : ByteArray
  deriving Inhabited

def proveM (_hash : Address) : ProveM Proof :=
  default -- TODO
