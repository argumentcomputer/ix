import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

/-- Local entry checks isolate the resource consumed by a helper. Whole-image
admission is checked separately; a smaller local limit need not admit unrelated
functions and literals elsewhere in the runtime prefix. -/
def resourceCases (image : Image) : IO Nat := do
  let count ← IO.mkRef 0
  let run (limits : Limits) (id : Nat) (args : Array Value) (expected : Except Error Value)
      (fuel := 200000) : IO Unit := do
    let initial := enter limits image.program id args
    let actual := initial.bind fun frame => Ix.Ixby.run limits image.program fuel ⟨.eval frame, #[]⟩
    let fast := initial.bind fun frame =>
      (Compilatrix.Ixby.Runtime.Chunked.run limits image.program fuel
        (Compilatrix.Ixby.Runtime.Chunked.State.ofReference ⟨.eval frame, #[]⟩)).map
          Compilatrix.Ixby.Runtime.Chunked.Value.toReference
    need (same actual fast) s!"native local execution disagrees at {id}"
    need (same actual expected) s!"native local resource {id}: expected {reprStr expected}, got {reprStr actual}"
    count.modify (· + 1)
  for id in #[0, 1] do
    let args := if id == 0 then #[natural 7, word 3, word 11] else #[word 7, natural 3, natural 11]
    let result := if id == 0 then word 32 else natural 32
    run { locals := 6, continuations := 0, byteArrayBytes := 0 } id args (.ok result) 5
    run { locals := 5 } id args (.error (.limit .locals))
    run {} id args (.error .outOfFuel) 4
  for bits in #[32, 64, 128, 4096] do
    let largest := 2 ^ bits - 1
    run { natBits := bits } 4 #[natural largest] (.ok (word 0xffffffff))
    run { natBits := bits } 4 #[natural (largest + 1)] (.error (.limit .natBits))
    run { natBits := bits } 7 #[natural largest] (.ok (.scalar (.field (Goldilocks.reduce largest))))
    run { natBits := bits } 7 #[natural (largest + 1)] (.error (.limit .natBits))
    run { natBits := bits } 12 #[natural largest, natural 1] (.error (.limit .natBits))
    run { natBits := bits } 13 #[natural 0, natural largest] (.ok (natural 0))
    run { natBits := bits } 15 #[natural largest, natural 0] (.ok (natural 0))
    run { natBits := bits } 16 #[natural largest, natural 0] (.ok (natural largest))
  run { natBits := 31 } 2 #[word 0xffffffff] (.error (.limit .natBits))
  run { natBits := 32 } 2 #[word 0xffffffff] (.ok (natural (2 ^ 32 - 1)))
  run { natBits := 63 } 6 #[.scalar (.field (Goldilocks.reduce (goldilocksModulus - 1)))]
    (.error (.limit .natBits))
  run { natBits := 64 } 6 #[.scalar (.field (Goldilocks.reduce (goldilocksModulus - 1)))]
    (.ok (natural (goldilocksModulus - 1)))
  run {} 4 #[word 7] (.error (.primitiveType .natToWord32))
  run {} 6 #[natural 7] (.error (.primitiveType .fieldToNat))
  run { natBits := 64 } 46 #[natural (2 ^ 64 - 1), natural 1] (.error (.limit .natBits))
  run { natBits := 65 } 46 #[natural (2 ^ 64 - 1), natural 1] (.ok (natural 0))
  run { natBits := 64 } 47 #[natural 0, natural 1] (.error (.limit .natBits))
  run { natBits := 65 } 47 #[natural 0, natural 1] (.ok (natural (2 ^ 64 - 1)))
  run { natBits := 64 } 20 #[natural (2 ^ 32), natural 2] (.error (.limit .natBits))
  run { natBits := 65 } 20 #[natural (2 ^ 32), natural 2] (.ok (natural (2 ^ 64)))
  run { natBits := 64 } 20 #[natural (2 ^ 63), natural 1] (.ok (natural (2 ^ 63)))
  run { natBits := 64 } 11 #[natural (2 ^ 32), natural 2, natural 0] (.error (.limit .natBits))
  let arrayId ← checked (image.ctorId `Ixby.Runtime.Array)
  let bytesId ← checked (image.ctorId `Ixby.Runtime.Bytes)
  let writerId ← checked (image.ctorId `Ixby.Runtime.WriterBuffer)
  let array : Value := .ctor arrayId #[.array #[natural 7, natural 9]]
  let packed : Value := .ctor bytesId #[.scalar (.bytes #[1, 2, 3]), natural 3]
  let writer : Value := .ctor writerId #[.byteBuilder #[1, 2, 3]]
  run { natBits := 1 } 58 #[.erased, array] (.error (.limit .natBits))
  run { natBits := 2 } 58 #[.erased, array] (.ok (natural 2))
  run { continuations := 0 } 62 #[.erased, array, natural 0, .erased]
    (.ok (natural 7))
  run { continuations := 1 } 62 #[.erased, array, natural 1, .erased] (.ok (natural 9))
  for (input, result, locals, fuel) in #[(array, natural 7, 8, 7),
      (packed, word 1, 9, 7), (writer, word 1, 10, 9)] do
    run { locals, continuations := 0 } 62 #[.erased, input, natural 0, .erased] (.ok result) fuel
    run { locals := locals - 1, continuations := 0 } 62 #[.erased, input, natural 0, .erased]
      (.error (.limit .locals))
    for index in #[3, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 256] do
      run { locals := 7, continuations := 0 } 62 #[.erased, input, natural index, .erased]
        (.error .notConstructor)
  run { natBits := 1 } 62 #[.erased, array, natural 0, .erased] (.error (.limit .natBits))
  run { natBits := 2 } 62 #[.erased, array, natural 0, .erased] (.error (.limit .natBits))
  run { byteArrayBytes := 2 } 62 #[.erased, writer, word 0, .erased]
    (.error (.limit .byteArrayBytes))
  run { natBits := 1 } 62 #[.erased, writer, word 0, .erased] (.error (.limit .natBits))
  run { byteArrayBytes := 0 } 62 #[.erased, packed, natural 3, .erased] (.error .notConstructor)
  run { byteArrayBytes := 0 } 62 #[.erased, packed, natural 0, .erased]
    (.error (.limit .byteArrayBytes))
  run { byteArrayBytes := 0 } 62 #[.erased, writer, natural 3, .erased]
    (.error (.limit .byteArrayBytes))
  run {} 69 #[.erased, array, natural (2 ^ 256), natural 1] (.ok array)
  run {} 62 #[.erased, array, natural (2 ^ 256), .erased] (.error .notConstructor)
  run { byteArrayBytes := 2 } 51 #[writer] (.error (.limit .byteArrayBytes))
  run { byteArrayBytes := 3 } 51 #[writer] (.ok (.scalar (.bytes #[1, 2, 3])))
  run { natBits := 1 } 51 #[writer] (.error (.limit .natBits))
  run { byteArrayBytes := 3 } 82 #[.scalar (.bytes #[1, 2]), .scalar (.bytes #[3])]
    (.ok (.scalar (.bytes #[1, 2, 3])))
  run { byteArrayBytes := 2 } 82 #[.scalar (.bytes #[1, 2]), .scalar (.bytes #[3])]
    (.error (.limit .byteArrayBytes))
  run { locals := 2, byteArrayBytes := 0 } 51 #[packed] (.error (.limit .locals))
  run { locals := 3, byteArrayBytes := 0 } 51 #[packed] (.ok (.scalar (.bytes #[1, 2, 3])))
  let fieldRow : Array Value := #[natural 7, natural (goldilocksModulus - 1)]
  let rowBytes : Array UInt8 := #[7, 0, 0, 0, 0, 0, 0, 0] ++
    MultiStark.Verify.Codec.Wire.littleEndian 8 (goldilocksModulus - 1)
  let rowDigest : Value := .ctor bytesId #[.scalar (.bytes (Ix.Ixby.Blake3.hash rowBytes)), natural 32]
  let row : Value := .ctor arrayId #[.array fieldRow]
  let loopArgs : Array Value := #[.array fieldRow, natural 0, natural 2, .byteBuilder #[]]
  run { locals := 10, continuations := 0, natBits := 64, byteArrayBytes := 16 } 108 loopArgs
    (.ok (.scalar (.bytes rowBytes)))
  run { locals := 9, natBits := 64 } 108 loopArgs (.error (.limit .locals))
  run { natBits := 63 } 108 loopArgs (.error (.limit .natBits))
  run { natBits := 64, byteArrayBytes := 15 } 108 loopArgs (.error (.limit .byteArrayBytes))
  run { locals := 10, continuations := 1, natBits := 64, byteArrayBytes := 32 } 109 #[row] (.ok rowDigest)
  run { locals := 10, continuations := 0, natBits := 64 } 109 #[row] (.error (.limit .continuations))
  run { locals := 9, continuations := 1, natBits := 64 } 109 #[row] (.error (.limit .locals))
  run { natBits := 64, byteArrayBytes := 31 } 109 #[row] (.error (.limit .byteArrayBytes))
  run {} 109 #[packed] (.error .notConstructor)
  run {} 109 #[writer] (.error .notConstructor)
  IO.println s!"native resources: {← count.get} exact local, continuation, byte, scalar and fuel cases"
  return ← count.get

end CompilatrixTests.Ixby.Native
