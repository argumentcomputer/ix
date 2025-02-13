import Ix.Address

inductive ProveError
  | todo

instance : ToString ProveError := ⟨fun _ => "TODO"⟩

abbrev ProveM := ExceptT ProveError IO

structure Proof where
  inp : Address
  out : Address
  typ : Address
  /-- Bytes of the Binius proof -/
  bin : ByteArray
  deriving Inhabited

def proveM (_hash : Address) : ProveM Proof :=
  default -- TODO
