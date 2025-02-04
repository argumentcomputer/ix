import Std

abbrev Digest := ByteArray

inductive ProveError
  | mk

abbrev ProveM := ExceptT ProveError IO

structure Proof where
  inp : Digest
  out : Digest
  typ : Digest
  bin : ByteArray
  deriving Inhabited

def proveM (_hash : Digest) : ProveM Proof :=
  default -- TODO
