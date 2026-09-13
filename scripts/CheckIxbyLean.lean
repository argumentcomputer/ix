import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.Examples
import Compilatrix.Ixby.Runtime.Wire
import Compilatrix.Tools.Check

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Compilatrix.Ixby.Runtime.Examples

private def compileImage (env : Environment) (name : Name) (wire := false) : IO Image := do
  let (result, _) ← (compile name
    (setup := if wire then Compilatrix.Ixby.Runtime.buildWire else pure ())).toIO
    { fileName := "typed Ixby regression", fileMap := default, maxRecDepth := 16384, maxHeartbeats := 0 }
    { env }
  checked result

private def compileRejects (env : Environment) (name : Name) (limits : Ix.Ixby.Limits)
    (message : String) : IO Unit := do
  let (result, _) ← (compile name limits).toIO
    { fileName := "typed Ixby rejection", fileMap := default, maxHeartbeats := 0 } { env }
  match result with
  | .ok _ => throw (IO.userError s!"unexpected typed Ixby admission of {name}")
  | .error actual => need (actual == message) s!"unexpected compiler rejection: {actual}"

private def runNumber (image : Image) (args : Array Ix.Ixby.Value) (expected : Nat) : IO Unit := do
  let output ← checked <| (Ix.Ixby.execute image.state.limits image.program args 20000000).mapError reprStr
  let result ← checked (image.decodeNumber output)
  need (result == expected) s!"{image.sourceEntry}: expected {expected}, got {result}"

private def runBytes (image : Image) (args : Array Ix.Ixby.Value) (expected : Array UInt8) : IO Unit := do
  let output ← checked <| (Ix.Ixby.execute image.state.limits image.program args 20000000).mapError reprStr
  let some entry := image.state.functionNames[`Ixby.Runtime.toBytes]? |
    throw (IO.userError "missing byte decoder")
  let output ← checked <| (Ix.Ixby.execute image.state.limits { image.program with entry }
    #[output] 20000000).mapError reprStr
  need (output == .scalar (.bytes expected)) s!"{image.sourceEntry}: byte output differs"

private def numberList (image : Image) (values : List Nat) : Except String Ix.Ixby.Value := do
  let nil ← image.ctorId `List.nil
  let cons ← image.ctorId `List.cons
  values.foldrM (fun n tail => do return .ctor cons #[← image.number n, tail]) (.ctor nil #[])

def main : IO UInt32 := cli "check-ixby-lean" do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Compilatrix.Ixby.Runtime.Examples }] {}
  compileRejects env `Nat.add { byteArrayBytes := 2 ^ 32 }
    "typed Ixby packed byte capacity must fit Word32 indices"
  compileRejects env `Float.add {} "unsupported typed runtime extern Float.add"
  let numbers := #[0, 1, 2, 7, 31, 255, 256, 65535, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 80 + 17]
  let mut count := 0
  for name in #[``cacheNatural, `UInt32.xor] do
    let image ← compileImage env name
    for digit in [:16] do
      for shift in [:8] do
        let n := digit * 16 ^ shift
        let args ← if name == ``cacheNatural then do
          pure #[← checked (image.number (2 ^ 80 + n))]
        else do pure #[← checked (image.number n), ← checked (image.number 0)]
        runNumber image args n
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
        runNumber image #[← checked (image.number (a % 2 ^ width)),
          ← checked (image.number (b % 2 ^ width))] (operation a b)
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
  let image ← compileImage env ``tailSum
  -- A small continuation limit detects accidental calls in tail position.
  let image := { image with state := { image.state with limits := { image.state.limits with continuations := 8 } } }
  for n in #[0, 1, 10000] do
    runNumber image #[← checked (image.number n), ← checked (image.number 0)] (tailSum n 0)
    count := count + 1
  IO.println s!"check-ixby-lean ok: {count} differential reference executions; 2 compiler rejections; source refinement uncertified"
