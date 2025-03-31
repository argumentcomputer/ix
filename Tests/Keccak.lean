import Ix.Keccak
import LSpec

open LSpec

abbrev input : ByteArray := ⟨#[0]⟩
abbrev expectedOutput : ByteArray := ⟨#[
  188, 54, 120, 158, 122, 30, 40, 20, 54, 70, 66, 41, 130, 143, 129, 125, 102, 18, 247, 180, 119, 214, 101, 145, 255, 150, 169, 224, 100, 188, 201, 138
]⟩

def hash :=
  let hasher := Keccak.Hasher.init ()
  let hasher' := Keccak.Hasher.update hasher input
  let output := Keccak.Hasher.finalize hasher'
  output

def Tests.Keccak.suite : List LSpec.TestSeq :=
[
  test "Keccak256 hash" (expectedOutput.data = hash.data)
]
