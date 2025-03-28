import Ix.Address
import Ix.Ixon.Serialize
import Ix.Common

inductive ProveError
  | todo

instance : ToString ProveError := ⟨fun _ => "TODO"⟩

abbrev ProveM := ExceptT ProveError IO

structure Claim where
  inp : Address
  out : Address
  typ : Address
  deriving Inhabited, BEq

instance : ToString Claim where
  toString c := s!"#{c.inp} ~> #{c.out} : #{c.typ}"

structure Proof where
  claim: Claim
  /-- Bytes of the Binius proof -/
  bin : ByteArray
  deriving Inhabited, BEq

instance : ToString Proof where
  toString p := s!"<{toString p.claim} := {hexOfBytes p.bin}>"

instance : Repr Proof where
  reprPrec p _ := toString p

def prove (claim : Claim) : ProveM Proof :=
  default -- TODO
