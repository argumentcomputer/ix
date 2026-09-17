import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

def arrayCases (image : Image) (check : Check) : IO Nat := do
  let arrayId ← checked (image.ctorId `Ixby.Runtime.Array)
  let bytesId ← checked (image.ctorId `Ixby.Runtime.Bytes)
  let writerId ← checked (image.ctorId `Ixby.Runtime.WriterBuffer)
  let nilId ← checked (image.ctorId `List.nil)
  let consId ← checked (image.ctorId `List.cons)
  let array (values : Array Value) : Value := .ctor arrayId #[.array values]
  let packed (bytes : Array UInt8) : Value := .ctor bytesId #[.scalar (.bytes bytes), natural bytes.size]
  let writer (bytes : Array UInt8) : Value := .ctor writerId #[.byteBuilder bytes]
  let list (values : Array Value) (tail : Value := .ctor nilId #[]) : Value :=
    values.toList.foldr (fun head tail => .ctor consId #[head, tail]) tail
  let pool : Array Value := #[.erased, word 0xc0ffee, boolean true, natural (2 ^ 256 + 17),
    packed #[0, 255, 19], .pap 0 #[natural 3], array #[.erased, natural 5]]
  let typeValue := pool[5]!
  let proofValue := pool[4]!
  let fallback := word 0x654321
  let mut rejected := 0
  for capacity in #[0, 1, 2, 31, 32, 2 ^ 32, 2 ^ 64, 2 ^ 256 + 1] do
    for id in #[60, 61] do check id #[typeValue, natural capacity] (array #[])
  for length in Array.range 34 ++ #[65, 257] do
    let source := (Array.range length).map fun i => pool[i % pool.size]!
    let encoded := array source
    for id in #[58, 59] do check id #[typeValue, encoded] (natural length)
    check 55 #[encoded] encoded
    check 68 #[typeValue, encoded, fallback] (array (source.push fallback))
    check 75 #[typeValue, encoded] (array source.pop)
    check 76 #[typeValue, list source] encoded
    check 77 #[typeValue, encoded] (list source)
    let suffix := #[natural 99, .erased]
    check 52 #[list source, array suffix] (array (suffix ++ source))
    check 53 #[encoded, natural length, list suffix] (list (source ++ suffix))
    for index in [:length] do
      for id in #[62, 63, 64, 65] do
        check id #[typeValue, encoded, natural index, proofValue] source[index]!
      for id in #[66, 67] do
        check id #[typeValue, fallback, encoded, natural index] source[index]!
      let changed := array (source.set! index fallback)
      check 69 #[typeValue, encoded, natural index, fallback] changed
      check 70 #[typeValue, encoded, natural index, fallback, proofValue] changed
      -- The original is still passed after both updates.
      check 62 #[typeValue, encoded, natural index, proofValue] source[index]!
    for index in #[length, length + 1, 2 ^ 32, 2 ^ 64, 2 ^ 256] do
      check 69 #[typeValue, encoded, natural index, fallback] encoded
      for id in #[66, 67] do
        check id #[typeValue, fallback, encoded, natural index] fallback
      for id in #[62, 63, 64, 65] do
        expect image id #[typeValue, encoded, natural index, proofValue] (.error .notConstructor)
        rejected := rejected + 1
      expect image 70 #[typeValue, encoded, natural index, fallback, proofValue]
        (.error .notConstructor)
      rejected := rejected + 1
    for (start, stop) in #[(0, 0), (0, length), (1, length), (length / 2, length),
        (length + 1, length + 9), (length, 0), (0, 2 ^ 256), (2 ^ 256, 2 ^ 256 + 1)] do
      let expected := array (source.extract start stop)
      check 71 #[typeValue, encoded, natural start, natural stop] expected
      check 72 #[encoded, natural start, natural stop] expected
    for right in #[#[], #[fallback], source] do
      check 73 #[typeValue, encoded, array right] (array (source ++ right))
      check 74 #[encoded, array right] (array (source ++ right))
    check 56 #[encoded, natural 0, natural length, array suffix] (array (suffix ++ source))
    check 57 #[natural length, fallback, array suffix]
      (array (suffix ++ Array.replicate length fallback))
    check 78 #[typeValue, natural length, fallback] (array (Array.replicate length fallback))
  for length in #[0, 1, 3, 4, 7, 8, 15, 31, 32, 33, 65, 257] do
    let bytes := (Array.range length).map fun i => (i * 131 + 19).toUInt8
    let source := bytes.map fun b => word b.toUInt32
    let prefixBytes := #[0xaa, 0xbb, 0xcc]
    for encoded in #[packed bytes, array source, writer bytes] do
      check 51 #[encoded] (.scalar (.bytes bytes))
      check 58 #[typeValue, encoded] (natural length)
      check 55 #[encoded] (array source)
      for index in [:length] do
        check 62 #[typeValue, encoded, natural index, proofValue] source[index]!
        check 69 #[typeValue, encoded, natural index, fallback]
          (array (source.set! index fallback))
      check 68 #[typeValue, encoded, fallback] (array (source.push fallback))
    check 50 #[.array source, natural 0, natural length, .byteBuilder prefixBytes]
      (.scalar (.bytes (prefixBytes ++ bytes)))
    check 54 #[.scalar (.bytes bytes), natural 0, natural length, array #[fallback]]
      (array (#[fallback] ++ source))
    for (start, stop) in #[(0, length), (1, length), (length / 2, length),
        (length + 1, length + 2), (0, 2 ^ 64)] do
      let slice := bytes.extract start stop
      let expected := if slice.isEmpty then array #[] else packed slice
      check 72 #[packed bytes, natural start, natural stop] expected
    for other in #[#[], prefixBytes, bytes] do
      let joined := bytes ++ other
      check 74 #[packed bytes, packed other] (packed joined)
      check 82 #[.scalar (.bytes bytes), .scalar (.bytes other)] (.scalar (.bytes joined))
    check 79 #[packed bytes] (packed bytes)
    check 80 #[packed bytes] (packed bytes)
    check 81 #[packed bytes] (packed (Ix.Ixby.Blake3.hash bytes))
  return rejected

end CompilatrixTests.Ixby.Native
