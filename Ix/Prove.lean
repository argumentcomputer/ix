import Ix.Address
import Ix.Ixon.Serialize

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

instance : Ixon.Serialize Proof where
  put proof := proof.inp.hash ++ proof.out.hash ++ proof.typ.hash ++ proof.bin
  get bytes :=
    let inpBytes := bytes.extract 0 32
    let outBytes := bytes.extract 32 64
    let typBytes := bytes.extract 64 96
    let binBytes := bytes.extract 96 bytes.size
    .ok ⟨⟨inpBytes⟩, ⟨outBytes⟩, ⟨typBytes⟩, binBytes⟩

def prove (_hash : Address) : ProveM Proof :=
  default -- TODO
