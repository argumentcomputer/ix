import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Native

open Ix.Ixby Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

def wireCases (image : Image) (check : Check) : IO Unit := do
  let ctor (name : Lean.Name) (fields : Array Value) : IO Value := do
    return .ctor (← checked (image.ctorId name)) fields
  let arrayId ← checked (image.ctorId `Ixby.Runtime.Array)
  let bytesId ← checked (image.ctorId `Ixby.Runtime.Bytes)
  let writerId ← checked (image.ctorId `Ixby.Runtime.WriterBuffer)
  let stateId ← checked (image.ctorId `MultiStark.Verify.Codec.Wire.WriteState.mk)
  let readId ← checked (image.ctorId `MultiStark.Verify.Codec.Wire.ReadState.mk)
  let packed (bytes : Array UInt8) : Value := .ctor bytesId #[.scalar (.bytes bytes), natural bytes.size]
  let array (bytes : Array UInt8) : Value := .ctor arrayId #[.array (bytes.map fun b => word b.toUInt32)]
  let writer (bytes : Array UInt8) : Value := .ctor writerId #[.byteBuilder bytes]
  let state (buffer : Value) (limit : Nat) : Value :=
    .ctor stateId #[buffer, natural limit, natural 17, natural 29]
  let readState (buffer : Value) (offset : Nat) : Value :=
    .ctor readId #[buffer, natural offset, natural 17, natural 29]
  let okay (value : Value) := ctor `Except.ok #[value]
  let error (name : Lean.Name) : IO Value := do ctor `Except.error #[← ctor name #[]]
  let pair (a b : Value) := ctor `Prod.mk #[a, b]
  let unit ← ctor `PUnit.unit #[]
  for width in #[0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 31, 32, 65] do
    for n in #[0, 1, 255, 2 ^ 32 - 1, 2 ^ 32, goldilocksModulus - 1, 2 ^ 64,
        2 ^ 128 - 1, 2 ^ 512 - 1] do
      let expected := MultiStark.Verify.Codec.Wire.littleEndian width n
      check 102 #[natural width, natural n] (packed expected)
      check 98 #[natural width, natural n, .byteBuilder #[0x12, 0x34]]
        (.scalar (.bytes (#[0x12, 0x34] ++ expected)))
      for encoded in #[packed expected, array expected] do
        check 103 #[encoded] (natural (MultiStark.Verify.Codec.Wire.fromLittleEndian expected))
      check 99 #[.scalar (.bytes expected), word width.toUInt32, natural 7]
        (natural (7 * 256 ^ width + MultiStark.Verify.Codec.Wire.fromLittleEndian expected))
  for before in #[#[], #[0], #[1, 2, 3], (Array.range 31).map Nat.toUInt8] do
    for chunk in #[#[], #[0xff], #[0, 128, 255], (Array.range 34).map Nat.toUInt8] do
      let joined := before ++ chunk
      for limit in #[0, joined.size - 1, joined.size, joined.size + 1] do
        for input in #[packed chunk, array chunk] do
          let expected ← if joined.size ≤ limit then okay (← pair unit (state (writer joined) limit))
            else error `MultiStark.Verify.DecodeError.byteLimit
          check 101 #[input, state (writer before) limit] expected
        let expected ← if joined.size ≤ limit then okay (← pair unit (state (packed joined) limit))
          else error `MultiStark.Verify.DecodeError.byteLimit
        check 101 #[packed chunk, state (packed before) limit] expected
      let limits ← ctor `MultiStark.Verify.DecodeLimits.mk #[natural chunk.size, natural 17, natural 29]
      check 100 #[limits, .pap 101 #[packed chunk]] (← okay (packed chunk))
      check 107 #[packed joined, array joined] (boolean true)
      check 107 #[packed joined, packed (joined.push 99)] (boolean false)
    for byte in #[0, 1, 127, 128, 255] do
      let joined := before.push byte
      check 104 #[word byte.toUInt32, state (writer before) joined.size]
        (← okay (← pair unit (state (writer joined) joined.size)))
  for n in #[0, 1, 2 ^ 32 - 1, 2 ^ 32, goldilocksModulus - 2, goldilocksModulus - 1,
      goldilocksModulus, goldilocksModulus + 1, 2 ^ 64 - 1] do
    let bytes := MultiStark.Verify.Codec.Wire.littleEndian 8 n
    for offset in #[0, 1, 3] do
      let all := Array.replicate offset 0xaa ++ bytes ++ #[0xbb]
      for encoded in #[packed all, array all] do
        let output ← if n < goldilocksModulus then
          okay (← pair (natural n) (readState encoded (offset + 8)))
        else error `MultiStark.Verify.DecodeError.field
        check 105 #[readState encoded offset] output
        check 105 #[readState encoded (offset + 2)] (← error `MultiStark.Verify.DecodeError.truncated)
    let value := Goldilocks.reduce n
    let joined := #[0xaa] ++ MultiStark.Verify.Codec.Wire.littleEndian 8 value.val
    check 106 #[natural value.val, state (writer #[0xaa]) 9]
      (← okay (← pair unit (state (writer joined) 9)))
    check 106 #[natural value.val, state (writer #[0xaa]) 8]
      (← error `MultiStark.Verify.DecodeError.byteLimit)

end CompilatrixTests.Ixby.Native
