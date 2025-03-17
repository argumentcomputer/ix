import Ix.Address
import Ix.Ixon.Serialize
import Ix.Common

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
  deriving Inhabited, BEq

instance : ToString Proof where
  toString p := s!"<#{p.inp} ~> #{p.out} : #{p.typ}>"

instance : Repr Proof where
  reprPrec p _ := toString p

def prove (_hash : Address) : ProveM Proof :=
  default -- TODO
