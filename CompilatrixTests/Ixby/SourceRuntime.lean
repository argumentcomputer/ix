import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.Examples
import Compilatrix.Ixby.Runtime.Wire
import Compilatrix.Ixby.Runtime.Field
import Compilatrix.Ixby.Runtime.Chunked.Execute
import Compilatrix.Tools.Check

namespace CompilatrixTests.Ixby.SourceRuntime

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Compilatrix.Ixby.Runtime.Examples

private def compileImage (env : Environment) (name : Name) (wire := false) : IO Image := do
  let (result, _) ← (compile name
    (setup := if wire then Compilatrix.Ixby.Runtime.buildWire else pure ())).toIO
    { fileName := "typed Ixby regression", fileMap := default, maxRecDepth := 16384, maxHeartbeats := 0 }
    { env }
  let image ← checked result
  return image

private def compileRejects (env : Environment) (name : Name) (limits : Ix.Ixby.Limits)
    (message : String) : IO Unit := do
  let (result, _) ← (compile name limits).toIO
    { fileName := "typed Ixby rejection", fileMap := default, maxHeartbeats := 0 } { env }
  match result with
  | .ok _ => throw (IO.userError s!"unexpected typed Ixby admission of {name}")
  | .error actual => need (actual == message) s!"unexpected compiler rejection: {actual}"

private def checkedExecution (limits : Ix.Ixby.Limits) (program : Ix.Ixby.Program)
    (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
  let reference := Ix.Ixby.execute limits program args 20000000
  let chunked := Compilatrix.Ixby.Runtime.Chunked.execute limits program args 20000000
  need (match reference, chunked with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false) s!"chunked/source runtime disagreement at function {program.entry}"
  checked (reference.mapError reprStr)

private def runNumber (image : Image) (args : Array Ix.Ixby.Value) (expected : Nat) : IO Unit := do
  let output ← checkedExecution image.state.limits image.program args
  let result ← checked (image.decodeNumber output)
  need (result == expected) s!"{image.sourceEntry}: expected {expected}, got {result}"

private def runWord (image : Image) (args : Array Ix.Ixby.Value) (expected : Nat) : IO Unit := do
  let output ← checkedExecution image.state.limits image.program args
  let result ← checked (image.decodeWord output)
  need (result.toNat == expected) s!"{image.sourceEntry}: expected {expected}, got {result}"

private def runBytes (image : Image) (args : Array Ix.Ixby.Value) (expected : Array UInt8) : IO Unit := do
  let output ← checkedExecution image.state.limits image.program args
  let some entry := image.state.functionNames[`Ixby.Runtime.toBytes]? |
    throw (IO.userError "missing byte decoder")
  let output ← checkedExecution image.state.limits { image.program with entry } #[output]
  need (output == .scalar (.bytes expected)) s!"{image.sourceEntry}: byte output differs"

private def numberList (image : Image) (values : List Nat) : Except String Ix.Ixby.Value := do
  let nil ← image.ctorId `List.nil
  let cons ← image.ctorId `List.cons
  values.foldrM (fun n tail => do return .ctor cons #[← image.number n, tail]) (.ctor nil #[])

private def numberArray (image : Image) (values : Array Nat) : Except String Ix.Ixby.Value := do
  let array ← image.ctorId `Ixby.Runtime.Array
  return .ctor array #[.array (← values.mapM image.number)]

def run (certify : Image → IO Unit) (transform : Image → IO Image := pure) : IO Nat := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Compilatrix.Ixby.Runtime.Examples }] {}
  let compileImage (env : Environment) (name : Name) (wire := false) : IO Image := do
    let image ← compileImage env name wire
    certify image
    let result ← transform image
    certify result
    return result
  compileRejects env `Nat.add { byteArrayBytes := 2 ^ 32 }
    "typed Ixby packed byte capacity must fit Word32 indices"
  compileRejects env `Float.add {} "unsupported typed runtime extern Float.add"
  let numbers := #[0, 1, 2, 7, 31, 255, 256, 65535, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 80 + 17]
  let mut count := 0
  let fieldNumbers := numbers ++ #[Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus,
    Ix.Ixby.goldilocksModulus + 1]
  for (name, source) in #[(``fieldArithmetic, fieldArithmetic), (``fieldMixed, fieldMixed),
      (``extensionStorage, extensionStorage), (``fieldCompare, fieldCompare)] do
    let image ← compileImage env name
    for a in fieldNumbers do
      for b in fieldNumbers do
        runNumber image #[← checked (image.number a), ← checked (image.number b)] (source a b)
        count := count + 1
  let image ← compileImage env ``fieldPower
  for a in fieldNumbers do
    for b in #[0, 1, 2, 31, 65] do
      runNumber image #[← checked (image.number a), ← checked (image.number b)] (fieldPower a b)
      count := count + 1
  let image ← compileImage env ``extensionArithmetic
  for a in fieldNumbers do
    for b in fieldNumbers do
      for (c, d) in #[(a, b), (0, 0), (b, a)] do
        runNumber image #[← checked (image.number a), ← checked (image.number b),
          ← checked (image.number c), ← checked (image.number d)] (extensionArithmetic a b c d)
        count := count + 1
  for name in #[``cacheNatural, `UInt32.xor] do
    let image ← compileImage env name
    for digit in [:16] do
      for shift in [:8] do
        let n := digit * 16 ^ shift
        let args ← if name == ``cacheNatural then do
          pure #[← checked (image.number (2 ^ 80 + n))]
        else do pure #[image.word n.toUInt32, image.word 0]
        if name == ``cacheNatural then runNumber image args n else runWord image args n
        count := count + 1
  let image ← compileImage env ``deferredArithmetic
  for a in numbers do
    for b in numbers do
      runNumber image #[← checked (image.number a), ← checked (image.number b)] (deferredArithmetic a b)
      count := count + 1
  for (name, operation) in #[(`Nat.add, Nat.add), (`Nat.sub, Nat.sub), (`Nat.mul, Nat.mul),
      (`Nat.div, Nat.div), (`Nat.mod, Nat.mod)] do
    let image ← compileImage env name
    for a in numbers do
      for b in numbers do
        runNumber image #[← checked (image.number a), ← checked (image.number b)] (operation a b)
        count := count + 1
  for (name, operation) in #[
      (`UInt8.add, fun (a b : Nat) => (a.toUInt8 + b.toUInt8).toNat),
      (`UInt8.shiftLeft, fun (a b : Nat) => (a.toUInt8 <<< b.toUInt8).toNat),
      (`UInt32.sub, fun (a b : Nat) => (a.toUInt32 - b.toUInt32).toNat),
      (`UInt32.shiftLeft, fun (a b : Nat) => (a.toUInt32 <<< b.toUInt32).toNat),
      (`UInt32.shiftRight, fun (a b : Nat) => (a.toUInt32 >>> b.toUInt32).toNat)] do
    let image ← compileImage env name
    let width := if name.getPrefix == `UInt8 then 8 else 32
    for a in numbers do
      for b in #[0, 1, width - 1, width, width + 1, 255] do
        runWord image #[image.word (a % 2 ^ width).toUInt32,
          image.word (b % 2 ^ width).toUInt32] (operation a b)
        count := count + 1
  for (a, b) in #[(0, 0), (0, 7), (2, 0), (3, 31), (2 ^ 80, 1)] do
    let image ← compileImage env ``power
    runNumber image #[← checked (image.number a), ← checked (image.number b)] (power a b)
    count := count + 1
  let image ← compileImage env ``choose
  for n in numbers do
    runNumber image #[← checked (image.number n)] (choose n)
    count := count + 1
  let image ← compileImage env ``sumMapped
  for values in [[], [1], [1, 3, 7], List.range 33] do
    runNumber image #[← checked (image.number 11), ← checked (numberList image values)] (sumMapped 11 values)
    count := count + 1
  let image ← compileImage env ``arrayEdits
  for values in [[], [1], [1, 3, 7], List.range 33] do
    runNumber image #[← checked (numberList image values)] (arrayEdits values)
    count := count + 1
  let image ← compileImage env ``replicate
  for n in #[0, 1, 2, 3, 31, 32, 33, 257] do
    runNumber image #[← checked (image.number n)] (replicate n)
    count := count + 1
  for (name, expected) in #[(``byteSum, byteSum), (``byteHash, byteHash),
      (``widenBytes, widenBytes), (``boxBytes, boxBytes)] do
    let image ← compileImage env name
    for data in #[#[], #[0], #[0, 255, 128, 1], (Array.range 513).map Nat.toUInt8] do
      runNumber image #[← checked (image.bytes data)] (expected data)
      count := count + 1
  let image ← compileImage env ``byteSlices
  let data := (Array.range 33).map Nat.toUInt8
  for start in #[0, 1, 8, 32, 33, 34] do
    for stop in #[0, 1, 8, 32, 33, 34, 100] do
      runNumber image #[← checked (image.bytes data), ← checked (image.number start),
        ← checked (image.number stop)] (byteSlices data start stop)
      count := count + 1
  for (name, expected) in #[(``concatLeft, concatLeft), (``concatRight, concatRight),
      (``concatMixed, concatMixed)] do
    let image ← compileImage env name
    for data in #[#[], #[255], (Array.range 97).map Nat.toUInt8] do
      for n in #[0, 1, 2, 7, 17, 128, 513, 4097] do
        runBytes image #[← checked (image.bytes data), ← checked (image.number n)] (expected data n)
        count := count + 1
  let image ← compileImage env ``ropeEdits
  for n in #[0, 1, 17, 128] do
    runNumber image #[← checked (image.bytes data), ← checked (image.number n)] (ropeEdits data n)
    count := count + 1
  let image ← compileImage env `MultiStark.Verify.Codec.Wire.littleEndian true
  for width in #[0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 33] do
    for n in numbers do
      runBytes image #[← checked (image.number width), ← checked (image.number n)]
        (MultiStark.Verify.Codec.Wire.littleEndian width n)
      count := count + 1
  let image ← compileImage env `MultiStark.Verify.Codec.Wire.fromLittleEndian true
  for width in #[0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 33] do
    for n in numbers do
      let bytes := MultiStark.Verify.Codec.Wire.littleEndian width n
      runNumber image #[← checked (image.bytes bytes)] (MultiStark.Verify.Codec.Wire.fromLittleEndian bytes)
      count := count + 1
  let image ← compileImage env ``wireWriter true
  for bytes in #[#[], #[255], (Array.range 513).map Nat.toUInt8] do
    for limit in #[0, 1, bytes.size - 1, bytes.size, bytes.size + 1] do
      runBytes image #[← checked (image.bytes bytes), ← checked (image.number limit)] (wireWriter bytes limit)
      count := count + 1
  let image ← compileImage env ``wireCanonical true
  for left in #[#[], #[0], #[255], (Array.range 257).map Nat.toUInt8] do
    let changed := if left.isEmpty then left else left.set! 0 1
    for right in #[left, left.push 0, changed, left.pop] do
      runNumber image #[← checked (image.bytes left), ← checked (image.bytes right)] (wireCanonical left right)
      count := count + 1
  let image ← compileImage env ``wireFieldRead true
  for n in fieldNumbers do
    for width in #[0, 1, 7, 8, 9, 16] do
      let data := MultiStark.Verify.Codec.Wire.littleEndian width n
      for offset in #[0, 1, data.size, data.size + 1] do
        runNumber image #[← checked (image.bytes data), ← checked (image.number offset)]
          (wireFieldRead data offset)
        count := count + 1
  for (name, source) in #[(``wireFieldWrite, wireFieldWrite), (``wireFieldWriteRaw, wireFieldWriteRaw)] do
    let image ← compileImage env name true
    for n in fieldNumbers do
      for initial in #[#[], #[255], #[0, 128, 255]] do
        for limit in #[0, 7, 8, 9, 10, 11, 12] do
          runBytes image #[← checked (image.number n), ← checked (image.bytes initial),
            ← checked (image.number limit)] (source n initial limit)
          count := count + 1
  for wire in #[false, true] do
    let image ← compileImage env ``wireNatWrite wire
    for width in #[0, 1, 2, 3, 4, 5, 8, 9] do
      for n in #[0, 1, 255, 256, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 17] do
        for (initial, limit) in #[(#[], 8), (#[255], 9), (#[0, 128, 255], 3)] do
          runBytes image #[← checked (image.number width), ← checked (image.number n),
            ← checked (image.bytes initial), ← checked (image.number limit)] (wireNatWrite width n initial limit)
          count := count + 1
  for wire in #[false, true] do
    let image ← compileImage env ``rowHash wire
    for values in #[#[], #[0], #[1, Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus, 2 ^ 80 + 17],
        (Array.range 65).map (· * 1000003)] do
      runBytes image #[← checked (numberArray image values)] (rowHash values)
      count := count + 1
  let image ← compileImage env ``tailSum
  -- A small continuation limit detects accidental calls in tail position.
  let image := { image with state := { image.state with limits := { image.state.limits with continuations := 8 } } }
  for n in #[0, 1, 10000] do
    runNumber image #[← checked (image.number n), ← checked (image.number 0)] (tailSum n 0)
    count := count + 1
  IO.println s!"check-ixby-lean ok: {count} differential reference executions; 2 compiler rejections; source refinement uncertified"
  return count

end CompilatrixTests.Ixby.SourceRuntime
