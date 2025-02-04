import LSpec
import Ix.Blake3

def pairs : List $ (List UInt8 × List UInt8) := [
  ([0], [ 45,  58, 222, 223, 241,  27,  97, 241,
          76, 136, 110,  53, 175, 160,  54, 115,
         109, 205, 135, 167,  77,  39, 181, 193,
          81,   2,  37, 208, 245, 146, 226,  19,])
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (i, o) =>
    let input := ByteArray.mk ⟨i⟩
    let output := ByteArray.mk ⟨o⟩
    tSeq ++ (test s!"blake3 on {input}" $ input.blake3.data = output.data)
