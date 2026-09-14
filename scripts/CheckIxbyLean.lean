import Compilatrix.Ixby.LeanSound
import Compilatrix.Ixby.Runtime.Examples
import Compilatrix.Ixby.Runtime.Wire
import Compilatrix.Ixby.Runtime.Field
import Compilatrix.Tools.Check

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Compilatrix.Ixby.Runtime.Examples

private def compileImage (env : Environment) (name : Name) (wire := false) : IO Image := do
  let (result, _) ← (compile name
    (setup := if wire then Compilatrix.Ixby.Runtime.buildWire else pure ())).toIO
    { fileName := "typed Ixby regression", fileMap := default, maxRecDepth := 16384, maxHeartbeats := 0 }
    { env }
  let image ← checked result
  discard <| checked image.certifyNumberLayout
  discard <| checked image.certifyScalars
  discard <| checked image.certifyConversions
  return image

private def certificateMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyScalars
  let links := certified.links
  let changeFunction (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let reject (changed : Image) (label : String) (admitted := false) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
    match changed.certifyScalars with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"scalar certificate accepted {label}")
  reject (changeFunction links.mul fun fn => { fn with blocks := fn.blocks.modify 0 fun block =>
    { block with instruction := .letOp (.primitive .extAdd [.local 0, .local 1]) 1 } })
    "changed arithmetic primitive" true
  reject (changeFunction links.mul fun fn => { fn with blocks := fn.blocks.modify 1 fun block =>
    { block with instruction := .ret (.local 0) } }) "changed return operand" true
  reject (changeFunction links.first fun fn => { fn with blocks := fn.blocks.modify 0 fun block =>
    { block with instruction := .letOp (.primitive .extSnd [.local 0]) 1 } })
    "swapped field projection" true
  reject (changeFunction links.add fun fn => { fn with entry := 1 }) "changed entry"
  reject (changeFunction links.add fun fn => { fn with arity := 3 }) "changed arity"
  reject (changeFunction links.add fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } })
    "extra unreachable block" true
  let constructors := image.program.constructors.modify links.fieldBox fun ctor => { ctor with fields := 2 }
  reject { image with program := { image.program with constructors } }
    "changed constructor layout"
  let functionNames := image.state.functionNames.insert `Ix.Ixby.ExtGoldilocks.add links.sub
  reject { image with state := { image.state with functionNames } }
    "changed name binding" true
  IO.println "check-ixby-lean certificates: 7 generated functions; 8 rejected mutations"

private def conversionMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyConversions
  let links := certified.links
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
    match changed.certifyConversions with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"conversion certificate accepted {label}")
  reject (instruction links.toWord 6
    (.letOp (.primitive .natMod [.local 0, .literal (.nat 15)]) 7)) "wrong radix"
  reject (instruction links.toWord 11
    (.letOp (.primitive .word32Shl [.local 1, .literal (.word32 3)]) 12)) "wrong word weight"
  reject (instruction links.toWord 12 (.tailCall links.toWord [.local 9, .local 8, .local 10]))
    "swapped recursive arguments"
  reject (instruction links.fromWordLoop 3
    (.letOp (.primitive .word32And [.local 0, .literal (.word32 7)]) 4)) "wrong digit mask"
  reject (instruction links.fromWordLoop 9
    (.tailCall links.toWord [.local 8, .local 9, .local 7])) "wrong recursive callee"
  reject (instruction links.fromWord 1
    (.letOp (.construct links.cachedCtor [.local 0, .local 1]) 2)) "swapped cache fields"
  reject (instruction links.fromRaw 0
    (.letOp (.construct links.fieldCtor [.local 0]) 1)) "wrong number representation"
  reject (instruction links.lowWord 1 (.ret (.local 1))) "returned Nat as low word"
  reject (instruction links.natural 1 (.ret (.local 2))) "returned cache as exact Nat"
  reject (instruction links.fieldNatural 1
    (.letOp (.primitive .bytesSlice [.local 1, .literal (.word32 4), .literal (.word32 4)]) 2))
    "read high field word twice"
  reject (instruction links.asField 1 (.tailCall links.natural [.local 1])) "wrong field adapter"
  reject (instruction links.fieldFromNatural 0
    (.letOp (.primitive .natMod [.local 0, .literal (.nat (Ix.Ixby.goldilocksModulus - 1))]) 1))
    "wrong field modulus"
  reject (instruction links.nibbleWord 45 (.ret (.literal (.word32 14)))) "wrong digit leaf"
  reject (instruction links.nibbleNat 0
    (.letOp (.primitive .word32Lt [.local 0, .literal (.word32 7)]) 1)) "wrong digit pivot"
  reject (function links.nibbleWord fun fn => { fn with entry := 1 }) "changed entry" false
  reject (function links.fromWordLoop fun fn => { fn with arity := 2 }) "changed arity" false
  reject (function links.toWord fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } }) "extra block"
  let constructors := image.program.constructors.modify links.cachedCtor fun ctor => { ctor with fields := 1 }
  reject { image with program := { image.program with constructors } } "wrong cache layout" false
  let constructors := image.program.constructors.modify links.fieldCtor fun ctor =>
    { ctor with id := links.layout.raw }
  reject { image with program := { image.program with constructors } } "duplicate number tags" false
  let functionNames := image.state.functionNames.insert `Ixby.Runtime.fromWordLoop links.toWord
  reject { image with state := { image.state with functionNames } } "wrong function name binding"
  let constructorNames := image.state.constructorNames.insert `Ixby.Runtime.RawNumber links.fieldCtor
  reject { image with state := { image.state with constructorNames } } "wrong constructor name binding"
  IO.println "check-ixby-lean conversions: 11 generated functions; 21 rejected mutations (17 structurally admitted)"

private def conversionExecutions (image : Image) : IO Unit := do
  let certified ← checked image.certifyConversions
  let links := certified.links
  let count ← IO.mkRef 0
  let execute (id : Nat) (args : Array Ix.Ixby.Value) (expected : Ix.Ixby.Value) : IO Unit := do
    let program := { image.program with entry := id }
    discard <| checked (Compilatrix.Ixby.Runtime.Conversion.certify program links)
    let actual ← checked (Ix.Ixby.execute image.state.limits program args 20000 |>.mapError reprStr)
    need (actual == expected) s!"conversion helper {id}: expected {reprStr expected}, got {reprStr actual}"
    count.modify (· + 1)
  let numbers := #[0, 1, 15, 16, 17, 2 ^ 28 - 1, 2 ^ 28, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
    Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus, Ix.Ixby.goldilocksModulus + 1,
    2 ^ 64, 2 ^ 80 + 17, 2 ^ 256 + 255]
  for n in numbers do
    let word := n.toUInt32
    let cached : Ix.Ixby.Value := .ctor links.layout.cached #[.scalar (.nat n), .scalar (.word32 word)]
    let raw : Ix.Ixby.Value := .ctor links.layout.raw #[.scalar (.nat n)]
    execute links.toWord #[.scalar (.nat n), .scalar (.word32 1), .scalar (.word32 0)] (.scalar (.word32 word))
    execute links.fromWordLoop #[.scalar (.word32 word), .scalar (.nat 1), .scalar (.nat 0)]
      (.scalar (.nat word.toNat))
    execute links.fromWord #[.scalar (.word32 word)]
      (.ctor links.layout.cached #[.scalar (.nat word.toNat), .scalar (.word32 word)])
    execute links.fromRaw #[.scalar (.nat n)] raw
    execute links.fieldFromNatural #[.scalar (.nat n)] (.scalar (.field (Ix.Ixby.Goldilocks.reduce n)))
    for value in #[cached, raw] do
      execute links.natural #[value] (.scalar (.nat n))
      execute links.lowWord #[value] (.scalar (.word32 word))
      execute links.asField #[value] (.scalar (.field (Ix.Ixby.Goldilocks.reduce n)))
    let field := Ix.Ixby.Goldilocks.reduce n
    let value : Ix.Ixby.Value := .ctor links.layout.field #[.scalar (.field field)]
    execute links.natural #[value] (.scalar (.nat field.val))
    execute links.lowWord #[value] (.scalar (.word32 field.val.toUInt32))
    execute links.asField #[value] (.scalar (.field field))
  -- These are the local contracts' capacity thresholds. Whole-image admission
  -- above remains separate: unrelated functions can contain larger literals.
  let localCount ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 20000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"conversion resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    localCount.modify (· + 1)
  let small : Ix.Ixby.Limits := {
    image.state.limits with locals := 10, continuations := 2, natBits := 33, byteArrayBytes := 8 }
  let maxWord : UInt32 := 4294967295
  localRun small links.fromWord #[.scalar (.word32 maxWord)]
    (.ok (.ctor links.layout.cached #[.scalar (.nat maxWord.toNat), .scalar (.word32 maxWord)]))
  localRun { small with natBits := 32 } links.fromWord #[.scalar (.word32 maxWord)] (.error (.limit .natBits))
  localRun { small with locals := 9 } links.fromWord #[.scalar (.word32 maxWord)] (.error (.limit .locals))
  localRun { small with continuations := 1 } links.fromWord #[.scalar (.word32 maxWord)]
    (.error (.limit .continuations))
  let toWordLimits := { small with locals := 11, continuations := 1, natBits := 128 }
  let args : Array Ix.Ixby.Value := #[.scalar (.nat (2 ^ 80 + 17)), .scalar (.word32 1), .scalar (.word32 0)]
  localRun toWordLimits links.toWord args (.ok (.scalar (.word32 17)))
  localRun { toWordLimits with locals := 10 } links.toWord args (.error (.limit .locals))
  localRun { toWordLimits with continuations := 0 } links.toWord args (.error (.limit .continuations))
  let field := Ix.Ixby.Goldilocks.reduce (Ix.Ixby.goldilocksModulus - 1)
  localRun { small with natBits := 64 } links.fieldNatural #[.scalar (.field field)]
    (.ok (.scalar (.nat field.val)))
  localRun { small with natBits := 64, byteArrayBytes := 7 } links.fieldNatural #[.scalar (.field field)]
    (.error (.limit .byteArrayBytes))
  let fieldLimits := { small with locals := 11, natBits := 64, byteArrayBytes := 0 }
  localRun fieldLimits links.fieldFromNatural #[.scalar (.nat 1)]
    (.ok (.scalar (.field (Ix.Ixby.Goldilocks.reduce 1))))
  localRun { fieldLimits with natBits := 63 } links.fieldFromNatural #[.scalar (.nat 1)]
    (.error (.limit .natBits))
  IO.println s!"check-ixby-lean conversion contracts: {← count.get} admitted executions; {← localCount.get} resource cases"

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
  let runtimeImage ← compileImage env ``extensionArithmetic
  certificateMutations runtimeImage
  conversionMutations runtimeImage
  conversionExecutions runtimeImage
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
  let image ← compileImage env ``tailSum
  -- A small continuation limit detects accidental calls in tail position.
  let image := { image with state := { image.state with limits := { image.state.limits with continuations := 8 } } }
  for n in #[0, 1, 10000] do
    runNumber image #[← checked (image.number n), ← checked (image.number 0)] (tailSum n 0)
    count := count + 1
  IO.println s!"check-ixby-lean ok: {count} differential reference executions; 2 compiler rejections; source refinement uncertified"
