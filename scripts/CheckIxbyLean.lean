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
  discard <| checked image.certifyNatArithmetic
  discard <| checked image.certifyFields
  discard <| checked image.certifyNatLoops
  discard <| checked image.certifyWords
  discard <| checked image.certifyArrayTrees
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

private def natArithmeticMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyNatArithmetic
  let links := certified.links
  let conversions := links.conversions
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let rejected ← IO.mkRef 0
  let admittedCount ← IO.mkRef 0
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admittedCount.modify (· + 1)
    match changed.certifyNatArithmetic with
    | .error _ => rejected.modify (· + 1)
    | .ok _ => throw (IO.userError s!"Nat arithmetic certificate accepted {label}")
  reject (instruction links.add 0 (.letOp (.call conversions.lowWord [.local 0]) 1))
    "observed low word as exact Nat"
  reject (instruction links.add 1 (.letOp (.call conversions.natural [.local 0]) 2))
    "observed left operand twice"
  reject (instruction links.add 2 (.letOp (.primitive .natSub [.local 2, .local 3]) 3))
    "subtracted instead of added"
  reject (instruction links.add 7 (.letOp (.primitive .word32Sub [.local 6, .local 8]) 10))
    "inconsistent addition cache"
  reject (instruction links.add 10 (.letOp (.construct conversions.cachedCtor [.local 9, .local 4]) 11))
    "swapped result cache fields"
  reject (instruction links.add 11 (.ret (.local 0))) "returned input instead of sum"
  reject (instruction links.mul 2 (.letOp (.primitive .natAdd [.local 2, .local 3]) 3))
    "added instead of multiplied"
  reject (instruction links.mul 7 (.letOp (.primitive .word32Add [.local 6, .local 8]) 10))
    "inconsistent multiplication cache"
  reject (instruction links.mul 5 (.letOp (.construct conversions.fieldCtor [.local 4]) 14))
    "boxed exact Nat as native field"
  reject (instruction links.sub 2 (.letOp (.primitive .natLt [.local 3, .local 2]) 3))
    "reversed underflow comparison"
  reject (instruction links.sub 3 (.branch (.local 4) 5 4)) "swapped underflow branches"
  reject (instruction links.sub 4 (.letOp (.construct conversions.cachedCtor
    [.literal (.nat 0), .literal (.word32 1)]) 6)) "inconsistent underflow zero cache"
  reject (instruction links.sub 7 (.letOp (.call conversions.natural [.local 0]) 8))
    "repeated wrong subtraction operand"
  reject (instruction links.sub 8 (.letOp (.primitive .natAdd [.local 5, .local 6]) 9))
    "wrong non-underflow Nat primitive"
  reject (instruction links.sub 13 (.letOp (.primitive .word32Add [.local 9, .local 11]) 16))
    "wrong non-underflow cache primitive"
  reject (function links.mul fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } }) "extra block"
  reject (function links.sub fun fn => { fn with arity := 1 }) "changed arity" false
  reject (function links.add fun fn => { fn with entry := 1 }) "changed entry" false
  let functionNames := image.state.functionNames.insert `Nat.add links.mul
  reject { image with state := { image.state with functionNames } } "wrong arithmetic name binding"
  reject (instruction conversions.natural 1 (.ret (.local 2))) "changed conversion dependency"
  let constructors := image.program.constructors.modify conversions.cachedCtor fun ctor => { ctor with fields := 1 }
  reject { image with program := { image.program with constructors } } "changed constructor layout" false
  let constructorNames := image.state.constructorNames.insert `Ixby.Runtime.RawNumber conversions.fieldCtor
  reject { image with state := { image.state with constructorNames } } "wrong constructor name binding"
  reject (instruction links.div 2 (.letOp (.primitive .natMod [.local 2, .local 3]) 3))
    "remainder instead of quotient"
  reject (instruction links.div 2 (.letOp (.primitive .natDiv [.local 3, .local 2]) 3))
    "reversed division operands"
  reject (instruction links.div 1 (.letOp (.call conversions.natural [.local 0]) 2))
    "division observed dividend twice"
  reject (instruction links.div 3 (.tailCall conversions.fromWord [.local 4]))
    "division used word constructor"
  reject (instruction links.div 3 (.tailCall conversions.fromRaw [.local 2]))
    "division returned dividend"
  reject (instruction links.mod 2 (.letOp (.primitive .natDiv [.local 2, .local 3]) 3))
    "quotient instead of remainder"
  reject (instruction links.mod 2 (.letOp (.primitive .natMod [.local 2, .literal (.nat 1)]) 3))
    "remainder ignored divisor"
  reject (instruction links.mod 3 (.tailCall conversions.fromWord [.local 4]))
    "remainder used word constructor"
  reject (instruction links.equal 5 (.letOp (.primitive .natLt [.local 4, .local 5]) 6))
    "cached equality used less-than"
  reject (instruction links.equal 8 (.letOp (.primitive .natLt [.local 3, .local 4]) 9))
    "raw equality used less-than"
  reject (instruction links.equal 14 (.letOp (.primitive .natLt [.local 5, .local 6]) 15))
    "field/cached equality used less-than"
  reject (instruction links.equal 17 (.letOp (.primitive .natLt [.local 4, .local 5]) 18))
    "field/raw equality used less-than"
  reject (instruction links.equal 12 (.letOp (.primitive .fieldEq [.local 2, .local 2]) 19))
    "native field equality compared left operand to itself"
  reject (instruction links.equal 0 (.caseCtor (.local 1)
    [⟨conversions.cachedCtor, 1⟩, ⟨conversions.rawCtor, 2⟩, ⟨conversions.fieldCtor, 3⟩]))
    "equality dispatched on wrong operand"
  reject (instruction links.equal 1 (.letOp (.call conversions.asField [.local 0]) 4))
    "equality reduced an exact Nat"
  reject (instruction links.less 2 (.letOp (.primitive .natLt [.local 3, .local 2]) 3))
    "reversed less-than operands"
  reject (instruction links.less 3 (.ret (.local 0))) "less-than returned input"
  reject (instruction links.lessEqual 2 (.letOp (.primitive .natLt [.local 2, .local 3]) 3))
    "reversed less-or-equal operands"
  reject (instruction links.lessEqual 3 (.branch (.local 4) 5 4)) "swapped less-or-equal branches"
  reject (instruction links.lessEqual 4 (.ret (.literal (.bool true)))) "wrong less-or-equal false leaf"
  reject (function links.equal fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } })
    "extra equality block"
  let functionNames := image.state.functionNames.insert `Nat.div links.mod
  reject { image with state := { image.state with functionNames } } "wrong division name binding"
  let functionNames := image.state.functionNames.insert `Nat.decEq links.less
  reject { image with state := { image.state with functionNames } } "wrong equality name binding"
  reject (instruction conversions.fromRaw 0
    (.letOp (.construct conversions.fieldCtor [.local 0]) 1)) "changed division boxing dependency"
  reject (function links.equal fun fn => { fn with entry := 12 }) "changed equality entry" false
  reject (function links.less fun fn => { fn with arity := 1 }) "changed less-than arity" false
  IO.println s!"check-ixby-lean Nat arithmetic: 8 generated functions; {← rejected.get} rejected mutations ({← admittedCount.get} structurally admitted)"

private def natArithmeticExecutions (image : Image) : IO Unit := do
  let certified ← checked image.certifyNatArithmetic
  let links := certified.links
  let layout := links.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor layout.raw #[.scalar (.nat n)]
  let field (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.field #[.scalar (.field (Ix.Ixby.Goldilocks.reduce n))]
  let cases (n : Nat) : Array (Nat × Ix.Ixby.Value) :=
    #[(n, cached n), (n, raw n), (n % Ix.Ixby.goldilocksModulus, field n)]
  let operations : Array (Nat × (Nat → Nat → Ix.Ixby.Value)) := #[
    (links.add, fun a b => .scalar (.nat (a + b))),
    (links.sub, fun a b => .scalar (.nat (a - b))),
    (links.mul, fun a b => .scalar (.nat (a * b))),
    (links.div, fun a b => .scalar (.nat (a / b))),
    (links.mod, fun a b => .scalar (.nat (a % b))),
    (links.equal, fun a b => .scalar (.bool (a == b))),
    (links.less, fun a b => .scalar (.bool (decide (a < b)))),
    (links.lessEqual, fun a b => .scalar (.bool (decide (a ≤ b))))]
  let observe (value : Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    match value with
    | .scalar (.bool _) => return value
    | _ =>
      -- The image decoder independently checks any returned word cache.
      return .scalar (.nat (← checked (image.decodeNumber value)))
  let count ← IO.mkRef 0
  let execute (program : Ix.Ixby.Program) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    discard <| checked (Compilatrix.Ixby.Runtime.NatArithmetic.certify program links)
    checked (Ix.Ixby.execute image.state.limits program args 20000 |>.mapError reprStr)
  let numbers := #[0, 1, 2, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
    Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus, Ix.Ixby.goldilocksModulus + 1,
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 17, 2 ^ 256 + 255]
  for a in numbers do
    for b in numbers do
      for (a, left) in cases a do
        for (b, right) in cases b do
          for (id, operation) in operations do
            let actual ← execute { image.program with entry := id } #[left, right]
            let observed ← observe actual
            let expected := operation a b
            need (observed == expected)
              s!"Nat arithmetic helper {id}: {a}, {b}: expected {reprStr expected}, got {reprStr actual}"
            if id == links.div || id == links.mod then
              need (actual == .ctor layout.raw #[expected]) "division or remainder used the wrong representation"
            count.modify (· + 1)
  let callerCount ← IO.mkRef 0
  for (left, right) in #[(field (Ix.Ixby.goldilocksModulus - 1), raw (Ix.Ixby.goldilocksModulus + 1)),
      (cached (2 ^ 80 + 17), cached (2 ^ 32 + 1)), (raw 1, field 1),
      (field (Ix.Ixby.goldilocksModulus - 1), field 0)] do
    let a ← checked (image.decodeNumber left)
    let b ← checked (image.decodeNumber right)
    for (id, operation) in operations do
      -- A real caller retains both original operands around the helper call.
      -- Its final tree exposes the saved locals as well as the helper result.
      let caller : Ix.Ixby.Function := { arity := 2, blocks := #[
        ⟨2, .letOp (.call id [.local 0, .local 1]) 1⟩,
        ⟨3, .letOp (.construct links.conversions.cachedCtor [.local 1, .local 2]) 2⟩,
        ⟨4, .letOp (.construct links.conversions.cachedCtor [.local 0, .local 3]) 3⟩,
        ⟨5, .ret (.local 4)⟩] }
      let program := { image.program with
        entry := image.program.functions.size
        functions := image.program.functions.push caller }
      let actual ← execute program #[left, right]
      match actual with
      | .ctor _ #[savedLeft, .ctor _ #[savedRight, result]] =>
        need (savedLeft == left && savedRight == right) "Nat arithmetic caller lost a saved operand"
        need ((← observe result) == operation a b) "Nat arithmetic caller received the wrong result"
      | _ => throw (IO.userError "Nat arithmetic caller returned an unexpected tree")
      callerCount.modify (· + 1)
  let localCount ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 20000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"Nat arithmetic resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    localCount.modify (· + 1)
  let small : Ix.Ixby.Limits := {
    image.state.limits with locals := 14, continuations := 3, natBits := 64, byteArrayBytes := 8 }
  localRun { small with locals := 11 } links.add #[cached (2 ^ 32 - 1), cached 2] (.ok (cached (2 ^ 32 + 1)))
  localRun { small with locals := 10 } links.add #[cached (2 ^ 32 - 1), cached 2] (.error (.limit .locals))
  localRun { small with locals := 11 } links.mul #[cached (2 ^ 32 - 1), cached 2] (.ok (cached (2 ^ 33 - 2)))
  localRun { small with locals := 10 } links.mul #[cached (2 ^ 32 - 1), cached 2] (.error (.limit .locals))
  localRun small links.sub #[cached (2 ^ 32), cached 1] (.ok (cached (2 ^ 32 - 1)))
  localRun { small with locals := 13 } links.sub #[cached (2 ^ 32), cached 1] (.error (.limit .locals))
  localRun small links.sub #[raw 1, cached (2 ^ 32)] (.ok (cached 0))
  localRun small links.add #[cached (2 ^ 64 - 1), cached 1] (.error (.limit .natBits))
  localRun { small with natBits := 65 } links.add #[cached (2 ^ 64 - 1), cached 1] (.ok (cached (2 ^ 64)))
  localRun small links.mul #[cached (2 ^ 32), cached (2 ^ 32)] (.error (.limit .natBits))
  localRun { small with natBits := 65 } links.mul #[cached (2 ^ 32), cached (2 ^ 32)] (.ok (cached (2 ^ 64)))
  let maxField := field (Ix.Ixby.goldilocksModulus - 1)
  localRun small links.add #[maxField, cached 1] (.ok (raw Ix.Ixby.goldilocksModulus))
  localRun { small with continuations := 2 } links.add #[maxField, cached 1] (.error (.limit .continuations))
  localRun { small with byteArrayBytes := 7 } links.add #[cached 1, maxField] (.error (.limit .byteArrayBytes))
  localRun { small with natBits := 63 } links.add #[maxField, cached 0] (.error (.limit .natBits))
  let observationLimits := { small with locals := 10 }
  localRun observationLimits links.div #[maxField, raw 2] (.ok (raw ((Ix.Ixby.goldilocksModulus - 1) / 2)))
  localRun { observationLimits with locals := 9 } links.div #[maxField, raw 2] (.error (.limit .locals))
  localRun { observationLimits with continuations := 2 } links.div #[maxField, raw 2]
    (.error (.limit .continuations))
  localRun observationLimits links.div #[maxField, field 0] (.ok (raw 0))
  localRun observationLimits links.div #[cached 0, raw (2 ^ 64)] (.error (.limit .natBits))
  localRun observationLimits links.mod #[maxField, raw 7] (.ok (raw ((Ix.Ixby.goldilocksModulus - 1) % 7)))
  localRun observationLimits links.mod #[maxField, field 0] (.ok (raw (Ix.Ixby.goldilocksModulus - 1)))
  localRun { observationLimits with byteArrayBytes := 7 } links.mod #[cached 5, maxField]
    (.error (.limit .byteArrayBytes))
  localRun observationLimits links.less #[maxField, raw Ix.Ixby.goldilocksModulus] (.ok (.scalar (.bool true)))
  localRun { observationLimits with locals := 9 } links.less #[maxField, raw Ix.Ixby.goldilocksModulus]
    (.error (.limit .locals))
  localRun observationLimits links.lessEqual #[maxField, raw (Ix.Ixby.goldilocksModulus - 1)]
    (.ok (.scalar (.bool true)))
  localRun { observationLimits with continuations := 2 } links.lessEqual
    #[maxField, raw (Ix.Ixby.goldilocksModulus - 1)] (.error (.limit .continuations))
  localRun observationLimits links.equal #[raw Ix.Ixby.goldilocksModulus, field 0] (.ok (.scalar (.bool false)))
  localRun { observationLimits with byteArrayBytes := 7 } links.equal #[raw Ix.Ixby.goldilocksModulus, maxField]
    (.error (.limit .byteArrayBytes))
  -- Native field equality returns directly without Nat conversion or a call.
  let nativeEquality := { small with locals := 5, natBits := 0, byteArrayBytes := 0, continuations := 0 }
  localRun nativeEquality links.equal #[maxField, maxField] (.ok (.scalar (.bool true)))
  localRun nativeEquality links.equal #[maxField, field 0] (.ok (.scalar (.bool false)))
  localRun { nativeEquality with locals := 4 } links.equal #[maxField, maxField] (.error (.limit .locals))
  localRun { small with locals := 7 } links.equal #[cached 1, cached 1] (.ok (.scalar (.bool true)))
  localRun { small with locals := 6 } links.equal #[cached 1, cached 1] (.error (.limit .locals))
  localRun { observationLimits with continuations := 2 } links.equal #[raw Ix.Ixby.goldilocksModulus, maxField]
    (.error (.limit .continuations))
  IO.println s!"check-ixby-lean Nat arithmetic contracts: {← count.get} admitted executions; {← callerCount.get} caller cases; {← localCount.get} resource cases"

private def fieldMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyFields
  let links := certified.links
  let conversions := links.conversions
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let rejected ← IO.mkRef 0
  let admittedCount ← IO.mkRef 0
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admittedCount.modify (· + 1)
    match changed.certifyFields with
    | .error _ => rejected.modify (· + 1)
    | .ok _ => throw (IO.userError s!"field certificate accepted {label}")
  reject (instruction links.reduce 0 (.letOp (.call conversions.natural [.local 0]) 1))
    "reduction used exact Nat observer"
  reject (instruction links.reduce 1 (.letOp (.construct conversions.rawCtor [.local 1]) 2))
    "reduction used raw box"
  reject (instruction links.reduce 2 (.ret (.local 0))) "reduction returned input"
  reject (instruction links.add 0 (.letOp (.call conversions.lowWord [.local 0]) 1))
    "field addition observed low word"
  reject (instruction links.add 1 (.letOp (.call conversions.asField [.local 0]) 2))
    "field addition observed left input twice"
  reject (instruction links.add 2 (.letOp (.primitive .fieldSub [.local 2, .local 3]) 3))
    "field addition used subtraction"
  reject (instruction links.sub 2 (.letOp (.primitive .fieldSub [.local 3, .local 2]) 3))
    "field subtraction reversed operands"
  reject (instruction links.mul 2 (.letOp (.primitive .fieldAdd [.local 2, .local 3]) 3))
    "field multiplication used addition"
  reject (instruction links.mul 3 (.letOp (.construct conversions.rawCtor [.local 4]) 4))
    "field multiplication used raw box"
  reject (instruction links.neg 1
    (.letOp (.primitive .fieldSub [.local 1, .literal (.field 0)]) 2)) "negation reversed operands"
  reject (instruction links.neg 1
    (.letOp (.primitive .fieldSub [.literal (.field 1), .local 1]) 2)) "negation used wrong zero"
  reject (instruction links.inverse 1
    (.letOp (.primitive .fieldAdd [.local 1, .literal (.field 1)]) 2)) "inverse incremented input"
  reject (instruction links.inverse 2 (.letOp (.construct conversions.fieldCtor [.local 1]) 3))
    "inverse boxed input instead of result"
  reject (instruction links.pack 2 (.letOp (.primitive .fieldAdd [.local 2, .local 3]) 3))
    "extension packing used base-field addition"
  reject (instruction links.pack 2 (.letOp (.primitive .extPack [.local 3, .local 2]) 3))
    "extension packing reversed coefficients"
  reject (instruction links.pack 0 (.letOp (.call conversions.natural [.local 0]) 1))
    "extension packing used exact Nat observer"
  reject (instruction links.pack 1 (.letOp (.call conversions.asField [.local 0]) 2))
    "extension packing observed first coefficient twice"
  reject (instruction links.pack 3 (.ret (.local 2))) "extension packing returned a base field"
  reject (function links.neg fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } })
    "extra negation block"
  reject (function links.reduce fun fn => { fn with entry := 1 }) "changed reduction entry" false
  reject (function links.mul fun fn => { fn with arity := 1 }) "changed multiplication arity" false
  reject (function links.pack fun fn => { fn with arity := 3 }) "changed packing arity" false
  let functionNames := image.state.functionNames.insert `Ix.Ixby.Goldilocks.add links.sub
  reject { image with state := { image.state with functionNames } } "wrong base-field name binding"
  let functionNames := image.state.functionNames.insert `Ix.Ixby.ExtGoldilocks.mk links.add
  reject { image with state := { image.state with functionNames } } "wrong extension packing name binding"
  reject (instruction conversions.asField 1 (.ret (.local 1))) "conversion returned unreduced Nat"
  reject (instruction conversions.fieldFromNatural 0
    (.letOp (.primitive .natMod [.local 0, .literal (.nat (Ix.Ixby.goldilocksModulus - 1))]) 1))
    "conversion used wrong field modulus"
  let constructors := image.program.constructors.modify conversions.fieldCtor fun ctor => { ctor with fields := 2 }
  reject { image with program := { image.program with constructors } } "wrong field box layout" false
  let constructorNames := image.state.constructorNames.insert `Ixby.Runtime.FieldNumber conversions.rawCtor
  reject { image with state := { image.state with constructorNames } } "wrong field constructor name binding"
  let constructors := image.program.constructors.modify conversions.fieldCtor fun ctor => { ctor with id := conversions.layout.raw }
  reject { image with program := { image.program with constructors } } "duplicate number tags" false
  IO.println s!"check-ixby-lean fields: 7 generated functions; {← rejected.get} rejected mutations ({← admittedCount.get} structurally admitted)"

private def fieldExecutions (image : Image) : IO Unit := do
  let certified ← checked image.certifyFields
  let scalars ← checked image.certifyScalars
  let links := certified.links
  let layout := links.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor layout.raw #[.scalar (.nat n)]
  let boxed (field : Ix.Ixby.Goldilocks) : Ix.Ixby.Value := .ctor layout.field #[.scalar (.field field)]
  let field (n : Nat) : Ix.Ixby.Value := boxed (Ix.Ixby.Goldilocks.reduce n)
  let cases (n : Nat) : Array (Nat × Ix.Ixby.Value) :=
    #[(n, cached n), (n, raw n), (n % Ix.Ixby.goldilocksModulus, field n)]
  let unary : Array (Nat × (Nat → Ix.Ixby.Value)) := #[
    (links.reduce, field),
    (links.neg, fun n => boxed (Ix.Ixby.Goldilocks.reduce n).neg),
    (links.inverse, fun n => boxed (Ix.Ixby.Goldilocks.reduce n).inverse)]
  let binary : Array (Nat × (Nat → Nat → Ix.Ixby.Value)) := #[
    (links.add, fun a b => boxed ((Ix.Ixby.Goldilocks.reduce a).add (Ix.Ixby.Goldilocks.reduce b))),
    (links.sub, fun a b => boxed ((Ix.Ixby.Goldilocks.reduce a).sub (Ix.Ixby.Goldilocks.reduce b))),
    (links.mul, fun a b => boxed ((Ix.Ixby.Goldilocks.reduce a).mul (Ix.Ixby.Goldilocks.reduce b))),
    (links.pack, fun a b => .scalar (.extField ⟨Ix.Ixby.Goldilocks.reduce a, Ix.Ixby.Goldilocks.reduce b⟩))]
  let count ← IO.mkRef 0
  let execute (program : Ix.Ixby.Program) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    discard <| checked (Compilatrix.Ixby.Runtime.FieldArithmetic.certify program links)
    discard <| checked (Compilatrix.Ixby.Runtime.certifyScalars program scalars.links)
    checked (Ix.Ixby.execute image.state.limits program args 20000 |>.mapError reprStr)
  let numbers := #[0, 1, 2, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
    Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus, Ix.Ixby.goldilocksModulus + 1,
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 17, 2 ^ 256 + 255]
  for n in numbers do
    for (n, value) in cases n do
      for (id, operation) in unary do
        let actual ← execute { image.program with entry := id } #[value]
        let expected := operation n
        need (actual == expected) s!"unary field helper {id}: {n}: expected {reprStr expected}, got {reprStr actual}"
        count.modify (· + 1)
  for a in numbers do
    for b in numbers do
      for (a, left) in cases a do
        for (b, right) in cases b do
          for (id, operation) in binary do
            let actual ← execute { image.program with entry := id } #[left, right]
            let expected := operation a b
            need (actual == expected)
              s!"binary field helper {id}: {a}, {b}: expected {reprStr expected}, got {reprStr actual}"
            count.modify (· + 1)
  let callerCount ← IO.mkRef 0
  let withCaller (caller : Ix.Ixby.Function) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value :=
    execute { image.program with
      entry := image.program.functions.size
      functions := image.program.functions.push caller } args
  for value in #[cached (2 ^ 80 + 17), raw (Ix.Ixby.goldilocksModulus + 1), field (Ix.Ixby.goldilocksModulus - 1)] do
    let n ← checked (image.decodeNumber value)
    for (id, operation) in unary do
      -- The diagnostic result exposes the original caller local and result.
      let caller : Ix.Ixby.Function := { arity := 1, blocks := #[
        ⟨1, .letOp (.call id [.local 0]) 1⟩,
        ⟨2, .letOp (.construct links.conversions.cachedCtor [.local 0, .local 1]) 2⟩,
        ⟨3, .ret (.local 2)⟩] }
      let actual ← withCaller caller #[value]
      need (actual == .ctor layout.cached #[value, operation n]) "unary field caller lost input or result"
      callerCount.modify (· + 1)
  let projectionCount ← IO.mkRef 0
  for (left, right) in #[(field (Ix.Ixby.goldilocksModulus - 1), raw (Ix.Ixby.goldilocksModulus + 1)),
      (cached (2 ^ 80 + 17), cached (2 ^ 32 + 1)), (raw 1, field 2),
      (field (Ix.Ixby.goldilocksModulus - 1), field 0)] do
    let a ← checked (image.decodeNumber left)
    let b ← checked (image.decodeNumber right)
    for (id, operation) in binary do
      let caller : Ix.Ixby.Function := { arity := 2, blocks := #[
        ⟨2, .letOp (.call id [.local 0, .local 1]) 1⟩,
        ⟨3, .letOp (.construct links.conversions.cachedCtor [.local 1, .local 2]) 2⟩,
        ⟨4, .letOp (.construct links.conversions.cachedCtor [.local 0, .local 3]) 3⟩,
        ⟨5, .ret (.local 4)⟩] }
      let actual ← withCaller caller #[left, right]
      need (actual == .ctor layout.cached #[left, .ctor layout.cached #[right, operation a b]])
        "binary field caller lost input or result"
      callerCount.modify (· + 1)
    for (projection, expected) in #[(scalars.links.first, field a), (scalars.links.second, field b)] do
      let caller : Ix.Ixby.Function := { arity := 2, blocks := #[
        ⟨2, .letOp (.call links.pack [.local 0, .local 1]) 1⟩,
        ⟨3, .letOp (.call projection [.local 2]) 2⟩,
        ⟨4, .ret (.local 3)⟩] }
      need ((← withCaller caller #[left, right]) == expected) "packed extension projection changed coefficient order"
      projectionCount.modify (· + 1)
  -- Local capacity checks are separate from whole-image admission.
  let localCount ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 20000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"field resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    localCount.modify (· + 1)
  let small : Ix.Ixby.Limits := {
    image.state.limits with locals := 11, continuations := 3, natBits := 64, byteArrayBytes := 0 }
  localRun small links.reduce #[raw 1] (.ok (field 1))
  localRun { small with locals := 10 } links.reduce #[raw 1] (.error (.limit .locals))
  localRun { small with continuations := 2 } links.reduce #[raw 1] (.error (.limit .continuations))
  localRun { small with natBits := 63 } links.reduce #[cached 0] (.error (.limit .natBits))
  localRun small links.reduce #[raw (2 ^ 64)] (.error (.limit .natBits))
  localRun { small with natBits := 65 } links.reduce #[raw (2 ^ 64)] (.ok (field (2 ^ 64)))
  localRun small links.add #[raw (Ix.Ixby.goldilocksModulus - 1), cached 1] (.ok (field 0))
  localRun small links.sub #[cached 0, raw 1] (.ok (field (Ix.Ixby.goldilocksModulus - 1)))
  localRun small links.mul #[cached (Ix.Ixby.goldilocksModulus - 1), raw (Ix.Ixby.goldilocksModulus - 1)]
    (.ok (field 1))
  localRun small links.inverse #[cached 0] (.ok (field 0))
  localRun small links.inverse #[raw Ix.Ixby.goldilocksModulus] (.ok (field 0))
  localRun small links.pack #[raw (Ix.Ixby.goldilocksModulus + 1), cached (Ix.Ixby.goldilocksModulus + 2)]
    (.ok (.scalar (.extField ⟨1, 2⟩)))
  localRun { small with continuations := 2 } links.pack
    #[raw (Ix.Ixby.goldilocksModulus + 1), cached (Ix.Ixby.goldilocksModulus + 2)]
    (.error (.limit .continuations))
  -- Native field inputs use the direct observer branch without Nat conversion.
  let native := { small with natBits := 0, continuations := 1 }
  let maxField := field (Ix.Ixby.goldilocksModulus - 1)
  localRun { native with locals := 3 } links.reduce #[maxField] (.ok maxField)
  localRun { native with locals := 3, continuations := 0 } links.reduce #[maxField]
    (.error (.limit .continuations))
  localRun { native with locals := 6 } links.add #[maxField, field 1] (.ok (field 0))
  localRun { native with locals := 5 } links.add #[maxField, field 1] (.error (.limit .locals))
  localRun { native with locals := 4 } links.neg #[maxField] (.ok (field 1))
  localRun { native with locals := 3 } links.neg #[maxField] (.error (.limit .locals))
  localRun { native with locals := 4 } links.inverse #[maxField] (.ok maxField)
  localRun { native with locals := 4 } links.inverse #[field 0] (.ok (field 0))
  localRun { native with locals := 5 } links.pack #[maxField, field 1]
    (.ok (.scalar (.extField ⟨Ix.Ixby.Goldilocks.reduce (Ix.Ixby.goldilocksModulus - 1), 1⟩)))
  localRun { native with locals := 4 } links.pack #[maxField, field 1] (.error (.limit .locals))
  localRun native links.add #[cached 1, maxField] (.error (.limit .natBits))
  IO.println s!"check-ixby-lean field contracts: {← count.get} admitted executions; {← callerCount.get} caller cases; {← projectionCount.get} packing/projection cases; {← localCount.get} resource cases"

private def natLoopMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyNatLoops
  let links := certified.links
  let arithmetic := links.arithmetic
  let conversions := arithmetic.conversions
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let rejected ← IO.mkRef 0
  let admittedCount ← IO.mkRef 0
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admittedCount.modify (· + 1)
    match changed.certifyNatLoops with
    | .error _ => rejected.modify (· + 1)
    | .ok _ => throw (IO.userError s!"Nat loop certificate accepted {label}")
  reject (instruction links.shiftRightLoop 0
    (.letOp (.primitive .natEq [.local 0, .literal (.nat 0)]) 1)) "shift tested the value as the count"
  reject (instruction links.shiftRightLoop 1 (.branch (.local 2) 3 2)) "shift reversed termination branches"
  reject (instruction links.shiftRightLoop 2 (.tailCall conversions.natural [.local 0])) "shift omitted boxing"
  reject (instruction links.shiftRightLoop 5 (.letOp (.construct conversions.cachedCtor
    [.literal (.nat 0), .literal (.word32 1)]) 7)) "shift returned an inconsistent zero cache"
  reject (instruction links.shiftRightLoop 6
    (.letOp (.primitive .natDiv [.local 0, .literal (.nat 3)]) 8)) "shift divided by three"
  reject (instruction links.shiftRightLoop 8
    (.letOp (.primitive .natSub [.local 1, .literal (.nat 2)]) 9)) "shift skipped a bit"
  reject (instruction links.shiftRightLoop 9 (.tailCall links.shiftRightLoop [.local 5, .local 4]))
    "shift swapped recursive arguments"
  reject (instruction links.shiftRightLoop 9 (.tailCall links.log2Loop [.local 4, .local 5]))
    "shift used the logarithm loop"
  reject (instruction links.shiftRight 0 (.letOp (.call conversions.lowWord [.local 0]) 1))
    "shift observed the low word"
  reject (instruction links.shiftRight 1 (.letOp (.call conversions.natural [.local 0]) 2))
    "shift observed its value twice"
  reject (instruction links.shiftRight 2 (.tailCall links.shiftRightLoop [.local 3, .local 2]))
    "shift wrapper swapped value and count"
  reject (instruction links.log2Loop 0
    (.letOp (.primitive .natLt [.local 0, .literal (.nat 1)]) 1)) "logarithm used the wrong stopping threshold"
  reject (instruction links.log2Loop 2 (.tailCall conversions.fromRaw [.local 0])) "logarithm returned its input"
  reject (instruction links.log2Loop 3
    (.letOp (.primitive .natDiv [.local 0, .literal (.nat 3)]) 4)) "logarithm divided by three"
  reject (instruction links.log2Loop 4
    (.letOp (.primitive .natAdd [.local 1, .literal (.nat 2)]) 5)) "logarithm incremented twice"
  reject (instruction links.log2Loop 5 (.tailCall links.log2Loop [.local 4, .local 3]))
    "logarithm swapped recursive arguments"
  reject (instruction links.log2 1 (.tailCall links.log2Loop [.local 1, .literal (.nat 1)]))
    "logarithm started its accumulator at one"
  reject (instruction links.powLoop 2 (.ret (.local 0))) "zero exponent returned the base"
  reject (instruction links.powLoop 3
    (.letOp (.primitive .natDiv [.local 1, .literal (.nat 3)]) 4)) "power divided the exponent by three"
  reject (instruction links.powLoop 4
    (.letOp (.primitive .natMod [.local 1, .literal (.nat 3)]) 5)) "power used radix three"
  reject (instruction links.powLoop 5
    (.letOp (.primitive .natEq [.local 5, .literal (.nat 0)]) 6)) "power tested even instead of odd"
  reject (instruction links.powLoop 7 (.letOp (.call arithmetic.add [.local 2, .local 0]) 9))
    "power added its accumulator"
  reject (instruction links.powLoop 7 (.letOp (.call arithmetic.mul [.local 2, .local 2]) 9))
    "power multiplied the accumulator by itself"
  reject (instruction links.powLoop 9
    (.letOp (.primitive .natEq [.local 4, .literal (.nat 1)]) 10)) "power stopped one iteration early"
  reject (instruction links.powLoop 12 (.letOp (.call arithmetic.mul [.local 0, .local 2]) 13))
    "odd power branch did not square the base"
  reject (instruction links.powLoop 13 (.tailCall links.powLoop [.local 9, .local 1, .local 7]))
    "power retained the old exponent"
  reject (instruction links.powLoop 13 (.tailCall links.powLoop [.local 9, .local 4, .local 2]))
    "power discarded the new accumulator"
  reject (instruction links.powLoop 16 (.letOp (.call arithmetic.add [.local 0, .local 0]) 17))
    "even power branch doubled the base"
  reject (instruction links.powLoop 17 (.tailCall links.powLoop [.local 0, .local 4, .local 2]))
    "even power branch discarded the square"
  reject (instruction links.pow 0 (.letOp (.call conversions.natural [.local 0]) 1))
    "power observed the base as its exponent"
  reject (instruction links.pow 1 (.letOp (.construct conversions.cachedCtor
    [.literal (.nat 0), .literal (.word32 0)]) 2)) "power initialized the accumulator to zero"
  reject (instruction links.pow 1 (.letOp (.construct conversions.cachedCtor
    [.literal (.nat 1), .literal (.word32 0)]) 2)) "power initialized an inconsistent cache"
  reject (instruction arithmetic.mul 2 (.letOp (.primitive .natAdd [.local 2, .local 3]) 3))
    "multiplication dependency added"
  reject (instruction arithmetic.mul 7 (.letOp (.primitive .word32Add [.local 6, .local 8]) 10))
    "multiplication dependency corrupted its cache"
  reject (instruction conversions.natural 1 (.ret (.local 2))) "observer dependency returned a cache"
  reject (instruction conversions.fromRaw 0 (.letOp (.construct conversions.fieldCtor [.local 0]) 1))
    "boxing dependency used the field layout"
  reject (function links.powLoop fun fn =>
    { fn with blocks := fn.blocks.push { locals := 0, instruction := .ret .erased } }) "extra loop block"
  reject (function links.log2 fun fn => { fn with entry := 1 }) "changed logarithm entry" false
  reject (function links.powLoop fun fn => { fn with arity := 2 }) "changed power loop arity" false
  let functionNames := image.state.functionNames.insert `Nat.pow links.shiftRight
  reject { image with state := { image.state with functionNames } } "wrong public power name binding"
  let functionNames := image.state.functionNames.insert `Ixby.Runtime.shiftRightLoop links.log2Loop
  reject { image with state := { image.state with functionNames } } "wrong recursive name binding"
  let constructors := image.program.constructors.modify conversions.cachedCtor fun ctor => { ctor with fields := 1 }
  reject { image with program := { image.program with constructors } } "wrong cached layout" false
  let constructorNames := image.state.constructorNames.insert `Ixby.Runtime.RawNumber conversions.fieldCtor
  reject { image with state := { image.state with constructorNames } } "wrong raw constructor binding"
  let constructors := image.program.constructors.modify conversions.rawCtor fun ctor => { ctor with id := conversions.layout.cached }
  reject { image with program := { image.program with constructors } } "duplicate number tags" false
  IO.println s!"check-ixby-lean Nat loops: 6 generated functions; {← rejected.get} rejected mutations ({← admittedCount.get} structurally admitted)"

private def natLoopExecutions (image : Image) : IO Unit := do
  let certified ← checked image.certifyNatLoops
  let links := certified.links
  let layout := links.arithmetic.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor layout.raw #[.scalar (.nat n)]
  let field (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.field #[.scalar (.field (Ix.Ixby.Goldilocks.reduce n))]
  let cases (n : Nat) : Array (Nat × Ix.Ixby.Value) :=
    #[(n, cached n), (n, raw n), (n % Ix.Ixby.goldilocksModulus, field n)]
  let isCached : Ix.Ixby.Value → Bool
    | .ctor tag _ => tag == layout.cached
    | _ => false
  let shiftResult (n shift : Nat) :=
    if shift > 0 && n >>> (shift - 1) == 0 then cached 0 else raw (n >>> shift)
  -- Lean's native Nat.pow oracle rejects enormous exponents even for zero and
  -- one. Use the exact source laws for these constant-size mathematical results.
  let sourcePower (base exponent : Nat) :=
    if exponent == 0 then 1 else if base == 0 then 0 else if base == 1 then 1 else base ^ exponent
  let powerResult (base exponent accumulator : Nat) (baseValue accumulatorValue : Ix.Ixby.Value) :=
    if exponent == 0 then accumulatorValue
    else if isCached baseValue && isCached accumulatorValue then cached (accumulator * sourcePower base exponent)
    else raw (accumulator * sourcePower base exponent)
  let execute (program : Ix.Ixby.Program) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    discard <| checked (Compilatrix.Ixby.Runtime.NatLoops.certify program links)
    checked (Ix.Ixby.execute image.state.limits program args 200000 |>.mapError reprStr)
  let count ← IO.mkRef 0
  let runCase (id : Nat) (args : Array Ix.Ixby.Value) (expected : Ix.Ixby.Value) : IO Unit := do
    let actual ← execute { image.program with entry := id } args
    need (actual == expected) s!"Nat loop helper {id}: {reprStr args}: expected {reprStr expected}, got {reprStr actual}"
    -- Independently reject a stale word cache in any numeric result.
    discard <| checked (image.decodeNumber actual)
    count.modify (· + 1)
  let numbers := #[0, 1, 2, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1,
    Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus, Ix.Ixby.goldilocksModulus + 1,
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 17, 2 ^ 256 + 255]
  let shifts := #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 255, 256, 257,
    2 ^ 32, 2 ^ 64, 2 ^ 80 + 17]
  for n in numbers do
    for (n, value) in cases n do
      runCase links.log2 #[value] (raw n.log2)
      for shift in shifts do
        for (shift, amount) in cases shift do
          runCase links.shiftRight #[value, amount] (shiftResult n shift)
    for shift in shifts do
      runCase links.shiftRightLoop #[.scalar (.nat n), .scalar (.nat shift)] (shiftResult n shift)
    for accumulator in #[0, 1, 2 ^ 32, 2 ^ 80] do
      runCase links.log2Loop #[.scalar (.nat n), .scalar (.nat accumulator)] (raw (accumulator + n.log2))
  let powers (bases exponents : Array Nat) : IO Unit := do
    for base in bases do
      for exponent in exponents do
        for (base, value) in cases base do
          for (exponent, amount) in cases exponent do
            runCase links.pow #[value, amount] (powerResult base exponent 1 value (cached 1))
  powers numbers #[0, 1, 2, 3, 7, 8, 15]
  powers #[0, 1, 2, 3, 5, 7, 11] #[16, 31, 32, 33, 63, 64, 65, 127]
  powers #[0, 1] #[2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 80 + 17]
  for base in #[0, 1, 2, 2 ^ 32 + 1, Ix.Ixby.goldilocksModulus + 1] do
    for exponent in #[0, 1, 2, 3, 4, 5, 7, 8, 15, 16] do
      for accumulator in #[0, 1, 3, 2 ^ 80 + 17] do
        for (base, value) in cases base do
          for (accumulator, acc) in cases accumulator do
            runCase links.powLoop #[value, .scalar (.nat exponent), acc]
              (powerResult base exponent accumulator value acc)
  let callerCount ← IO.mkRef 0
  let callerCase (id : Nat) (args : Array Ix.Ixby.Value) (expected : Ix.Ixby.Value) : IO Unit := do
    let allArgs := args.push (.scalar (.word32 0xC0FFEE))
    let mut blocks : Array Ix.Ixby.Block := #[⟨allArgs.size,
      .letOp (.call id ((List.range args.size).map Ix.Ixby.Operand.local)) 1⟩]
    let mut result := allArgs.size
    let mut locals := allArgs.size + 1
    let mut expected := expected
    for i in (List.range allArgs.size).reverse do
      blocks := blocks.push ⟨locals, .letOp (.construct links.arithmetic.conversions.cachedCtor
        [.local i, .local result]) (blocks.size + 1)⟩
      result := locals
      locals := locals + 1
      expected := .ctor layout.cached #[allArgs[i]!, expected]
    blocks := blocks.push ⟨locals, .ret (.local result)⟩
    let caller : Ix.Ixby.Function := { arity := allArgs.size, blocks }
    let actual ← execute { image.program with
      entry := image.program.functions.size
      functions := image.program.functions.push caller } allArgs
    need (actual == expected) s!"Nat loop caller {id} lost an input, sentinel, or result"
    callerCount.modify (· + 1)
  for n in #[0, 1, 2 ^ 80 + 17] do
    for (n, value) in cases n do
      callerCase links.log2 #[value] (raw n.log2)
      callerCase links.shiftRight #[value, field 33] (shiftResult n 33)
      callerCase links.pow #[value, raw 3] (powerResult n 3 1 value (cached 1))
      callerCase links.powLoop #[value, .scalar (.nat 4), field 3] (powerResult n 4 3 value (field 3))
      callerCase links.powLoop #[value, .scalar (.nat 0), field 3] (field 3)
    callerCase links.shiftRightLoop #[.scalar (.nat n), .scalar (.nat 33)] (shiftResult n 33)
    callerCase links.log2Loop #[.scalar (.nat n), .scalar (.nat 7)] (raw (7 + n.log2))
  -- These local checks do not assume whole-image admission at smaller limits.
  let localCount ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 200000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"Nat loop resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    localCount.modify (· + 1)
  let shiftOnly : Ix.Ixby.Limits := {
    image.state.limits with locals := 6, continuations := 0, natBits := 2, byteArrayBytes := 0 }
  localRun shiftOnly links.shiftRightLoop #[.scalar (.nat 3), .scalar (.nat 1)] (.ok (raw 1))
  localRun { shiftOnly with locals := 5 } links.shiftRightLoop #[.scalar (.nat 3), .scalar (.nat 1)]
    (.error (.limit .locals))
  localRun { shiftOnly with natBits := 1 } links.shiftRightLoop #[.scalar (.nat 3), .scalar (.nat 1)]
    (.error (.limit .natBits))
  localRun shiftOnly links.shiftRightLoop #[.scalar (.nat 1), .scalar (.nat 1)] (.ok (raw 0))
  localRun shiftOnly links.shiftRightLoop #[.scalar (.nat 1), .scalar (.nat 2)] (.ok (cached 0))
  localRun { shiftOnly with locals := 3 } links.shiftRightLoop #[.scalar (.nat 3), .scalar (.nat 0)] (.ok (raw 3))
  localRun { shiftOnly with locals := 5 } links.shiftRightLoop #[.scalar (.nat 0), .scalar (.nat 3)] (.ok (cached 0))
  localRun { shiftOnly with locals := 4 } links.shiftRightLoop #[.scalar (.nat 0), .scalar (.nat 3)]
    (.error (.limit .locals))
  localRun { shiftOnly with natBits := 64 } links.shiftRightLoop
    #[.scalar (.nat 0), .scalar (.nat (2 ^ 64 - 1))] (.ok (cached 0))
  let logOnly := { shiftOnly with locals := 5, natBits := 64 }
  localRun logOnly links.log2Loop #[.scalar (.nat 0), .scalar (.nat 7)] (.ok (raw 7))
  localRun logOnly links.log2Loop #[.scalar (.nat 1), .scalar (.nat 7)] (.ok (raw 7))
  localRun logOnly links.log2Loop #[.scalar (.nat 3), .scalar (.nat (2 ^ 64 - 2))] (.ok (raw (2 ^ 64 - 1)))
  localRun logOnly links.log2Loop #[.scalar (.nat 2), .scalar (.nat (2 ^ 64 - 1))] (.error (.limit .natBits))
  localRun { logOnly with natBits := 65 } links.log2Loop
    #[.scalar (.nat 2), .scalar (.nat (2 ^ 64 - 1))] (.ok (raw (2 ^ 64)))
  localRun { logOnly with locals := 4 } links.log2Loop #[.scalar (.nat 4), .scalar (.nat 0)]
    (.error (.limit .locals))
  localRun { logOnly with natBits := 1 } links.log2Loop #[.scalar (.nat 0), .scalar (.nat 0)]
    (.error (.limit .natBits))
  let observed : Ix.Ixby.Limits := {
    image.state.limits with locals := 10, continuations := 3, natBits := 64, byteArrayBytes := 8 }
  let maxField := Ix.Ixby.goldilocksModulus - 1
  localRun observed links.log2 #[field maxField] (.ok (raw maxField.log2))
  localRun { observed with locals := 9 } links.log2 #[field maxField] (.error (.limit .locals))
  localRun { observed with continuations := 2 } links.log2 #[field maxField] (.error (.limit .continuations))
  localRun { observed with byteArrayBytes := 7 } links.log2 #[field maxField] (.error (.limit .byteArrayBytes))
  localRun { observed with natBits := 63 } links.log2 #[field maxField] (.error (.limit .natBits))
  localRun observed links.shiftRight #[field maxField, field 1] (.ok (raw (maxField >>> 1)))
  localRun { observed with continuations := 2 } links.shiftRight #[field maxField, field 1]
    (.error (.limit .continuations))
  localRun { observed with locals := 6, continuations := 1, byteArrayBytes := 0 }
    links.shiftRight #[cached 8, raw 3] (.ok (raw 1))
  localRun { observed with locals := 5, continuations := 1, byteArrayBytes := 0 }
    links.shiftRight #[cached 8, raw 3] (.error (.limit .locals))
  localRun { observed with continuations := 0 } links.shiftRight #[cached 8, raw 3]
    (.error (.limit .continuations))
  let power := { observed with locals := 11, continuations := 4 }
  localRun power links.pow #[cached 0, cached 0] (.ok (cached 1))
  localRun power links.pow #[field maxField, cached 0] (.ok (cached 1))
  localRun power links.pow #[cached (2 ^ 64 - 1), cached 1] (.ok (cached (2 ^ 64 - 1)))
  localRun power links.pow #[field maxField, cached 1] (.ok (raw maxField))
  localRun { power with continuations := 3 } links.pow #[field maxField, cached 1]
    (.error (.limit .continuations))
  localRun { power with byteArrayBytes := 7 } links.pow #[field maxField, cached 1]
    (.error (.limit .byteArrayBytes))
  localRun { power with locals := 10 } links.pow #[cached 2, cached 3] (.error (.limit .locals))
  localRun power links.pow #[cached 2, raw 63] (.ok (cached (2 ^ 63)))
  localRun power links.pow #[cached 2, raw 64] (.error (.limit .natBits))
  localRun { power with natBits := 65 } links.pow #[cached 2, raw 64] (.ok (cached (2 ^ 64)))
  localRun power links.pow #[cached (2 ^ 32), cached 2] (.error (.limit .natBits))
  localRun { power with natBits := 65 } links.pow #[cached (2 ^ 32), cached 2] (.ok (cached (2 ^ 64)))
  localRun power links.pow #[raw 0, cached (2 ^ 64 - 1)] (.ok (raw 0))
  localRun power links.pow #[cached 1, field maxField] (.ok (cached 1))
  -- A zero accumulated result alone does not bound the internal base square.
  localRun power links.powLoop #[cached (2 ^ 32), .scalar (.nat 2), cached 0] (.error (.limit .natBits))
  localRun { power with natBits := 65 } links.powLoop
    #[cached (2 ^ 32), .scalar (.nat 2), cached 0] (.ok (cached 0))
  localRun power links.powLoop #[cached (2 ^ 64 - 1), .scalar (.nat 1), cached 0] (.ok (cached 0))
  localRun power links.powLoop #[raw 0, .scalar (.nat 0), field maxField] (.ok (field maxField))
  localRun power links.powLoop #[field 3, .scalar (.nat 5), raw 7] (.ok (raw (7 * 3 ^ 5)))
  IO.println s!"check-ixby-lean Nat loop contracts: {← count.get} admitted executions; {← callerCount.get} caller cases; {← localCount.get} resource cases"

private def wordMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyWords
  let links := certified.links
  let conversions := links.conversions
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let rejected ← IO.mkRef 0
  let admittedCount ← IO.mkRef 0
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admittedCount.modify (· + 1)
    match changed.certifyWords with
    | .error _ => rejected.modify (· + 1)
    | .ok _ => throw (IO.userError s!"word certificate accepted {label}")
  let helpers : Array (Nat × Name) := #[(links.u8OfNat, `UInt8.ofNat), (links.u8ToNat, `UInt8.toNat), (links.u8ToU32, `UInt8.toUInt32), (links.u8Equal, `UInt8.decEq), (links.u8Add, `UInt8.add), (links.u8ShiftLeft, `UInt8.shiftLeft), (links.u8ShiftRight, `UInt8.shiftRight), (links.u32OfNat, `UInt32.ofNat), (links.u32OfNatLT, `UInt32.ofNatLT), (links.u32ToU8, `UInt32.toUInt8), (links.u32ToNat, `UInt32.toNat), (links.u32Add, `UInt32.add), (links.u32Sub, `UInt32.sub), (links.u32Mul, `UInt32.mul), (links.u32And, `UInt32.land), (links.u32Or, `UInt32.lor), (links.u32Xor, `UInt32.xor), (links.u32ShiftLeft, `UInt32.shiftLeft), (links.u32ShiftRight, `UInt32.shiftRight), (links.u32Equal, `UInt32.decEq), (links.u32Less, `UInt32.decLt), (links.usizeOfNat, `USize.ofNat), (links.usizeToNat, `USize.toNat), (links.usizeAdd, `USize.add), (links.usizeSub, `USize.sub), (links.usizeEqual, `USize.decEq), (links.usizeLess, `USize.decLt)]
  for (id, name) in helpers do
    let fn := image.program.functions[id]!
    reject (instruction id (fn.blocks.size - 1) (.ret .erased)) s!"changed return of {name}"
    let other := if id == links.u32Sub then links.u8ToNat else links.u32Sub
    let functionNames := image.state.functionNames.insert name other
    reject { image with state := { image.state with functionNames } } s!"wrong name binding for {name}"
  for id in #[conversions.toWord, conversions.fromWordLoop, conversions.fromWord, conversions.fromRaw,
      conversions.lowWord, conversions.natural, conversions.fieldNatural, conversions.asField,
      conversions.fieldFromNatural, conversions.nibbleWord, conversions.nibbleNat] do
    let fn := image.program.functions[id]!
    reject (instruction id (fn.blocks.size - 1) (.ret .erased)) s!"changed conversion dependency {id}"
  reject (instruction links.u8OfNat 2 (.letOp (.primitive .natDiv [.local 1, .literal (.nat 256)]) 3))
    "division instead of truncation"
  reject (instruction links.u8OfNat 3 (.letOp (.primitive .word32And [.local 2, .literal (.word32 254)]) 4))
    "incorrect byte cache mask"
  reject (instruction links.u32OfNat 2 (.letOp (.primitive .natMod [.local 1, .literal (.nat (2 ^ 16))]) 3))
    "incorrect UInt32 modulus"
  reject (instruction links.usizeOfNat 2 (.letOp (.primitive .natMod [.local 1, .literal (.nat (2 ^ 32))]) 3))
    "32-bit USize truncation"
  reject (instruction links.u32OfNatLT 0 (.letOp (.call conversions.natural [.local 1]) 1))
    "observed erased proof slot"
  reject (instruction links.u8Add 2 (.letOp (.call conversions.natural [.local 0]) 3))
    "observed left operand twice"
  reject (instruction links.u32Add 4 (.letOp (.primitive .natSub [.local 2, .local 4]) 5))
    "subtraction instead of addition"
  reject (instruction links.u32Mul 5 (.letOp (.primitive .word32Add [.local 3, .local 5]) 6))
    "stale product cache"
  reject (instruction links.usizeAdd 6 (.letOp (.construct conversions.cachedCtor [.local 7, .local 6]) 7))
    "swapped intermediate number components"
  reject (instruction links.u32Add 7 (.letOp (.call conversions.natural [.local 0]) 8))
    "truncated the original input"
  reject (instruction links.u8Add 8 (.letOp (.call conversions.lowWord [.local 0]) 9))
    "retained the original cache"
  reject (instruction links.u32Sub 4 (.letOp (.primitive .natAdd [.local 2, .literal (.nat (2 ^ 16))]) 5))
    "incorrect subtraction wrap"
  reject (instruction links.usizeSub 5 (.letOp (.primitive .natSub [.local 4, .local 6]) 6))
    "reversed Nat subtraction"
  reject (instruction links.u32Sub 6 (.letOp (.primitive .word32Sub [.local 5, .local 3]) 7))
    "reversed cache subtraction"
  reject (instruction links.u32And 2 (.letOp (.primitive .word32Or [.local 2, .local 3]) 3))
    "wrong logical primitive"
  reject (instruction links.u32Xor 3 (.tailCall conversions.fromRaw [.local 4])) "wrong logical result adapter"
  reject (instruction links.u8ShiftLeft 2 (.letOp (.primitive .word32And [.local 3, .literal (.word32 31)]) 3))
    "byte shift used the UInt32 count mask"
  reject (instruction links.u32ShiftRight 2 (.letOp (.primitive .word32And [.local 3, .literal (.word32 32)]) 3))
    "shift retained the out-of-range count bit"
  reject (instruction links.u32ShiftLeft 3 (.letOp (.primitive .word32Shr [.local 2, .local 4]) 4))
    "wrong shift direction"
  reject (instruction links.u8ShiftRight 4 (.letOp (.primitive .word32And [.local 5, .literal (.word32 254)]) 5))
    "byte shift corrupted its output mask"
  reject (instruction links.u32Equal 2 (.letOp (.primitive .natLt [.local 2, .local 3]) 3)) "wrong comparison"
  reject (function links.usizeSub fun fn => { fn with blocks := fn.blocks.push ⟨0, .ret .erased⟩ })
    "extra unreachable word block"
  reject (function links.u8ToNat fun fn => { fn with entry := 1 }) "changed identity entry" false
  reject (function links.u32OfNatLT fun fn => { fn with arity := 1 }) "omitted proof-slot arity" false
  let constructors := image.program.constructors.modify conversions.cachedCtor fun ctor => { ctor with fields := 1 }
  reject { image with program := { image.program with constructors } } "wrong cached layout" false
  let constructorNames := image.state.constructorNames.insert `Ixby.Runtime.RawNumber conversions.fieldCtor
  reject { image with state := { image.state with constructorNames } } "wrong raw constructor binding"
  let constructors := image.program.constructors.modify conversions.rawCtor fun ctor => { ctor with id := conversions.layout.cached }
  reject { image with program := { image.program with constructors } } "duplicate number tags" false
  IO.println s!"check-ixby-lean words: 27 generated functions; {← rejected.get} rejected mutations ({← admittedCount.get} structurally admitted)"

private def wordExecutions (image : Image) : IO Unit := do
  need (System.Platform.numBits == 64) "word source contracts require the compiler's 64-bit USize platform"
  let certified ← checked image.certifyWords
  let links := certified.links
  let layout := links.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor layout.raw #[.scalar (.nat n)]
  let field (n : Nat) : Ix.Ixby.Value :=
    .ctor layout.field #[.scalar (.field (Ix.Ixby.Goldilocks.reduce n))]
  let cases (n : Nat) : Array (Nat × Ix.Ixby.Value) :=
    #[(n, cached n), (n, raw n), (n % Ix.Ixby.goldilocksModulus, field n)]
  let execute (program : Ix.Ixby.Program) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    discard <| checked (Compilatrix.Ixby.Runtime.Words.certify program links)
    checked (Ix.Ixby.execute image.state.limits program args 200000 |>.mapError reprStr)
  let count ← IO.mkRef 0
  let registered ← IO.mkRef ({} : Std.HashMap Nat Nat)
  let callerCases ← IO.mkRef (#[] : Array (Nat × Array Ix.Ixby.Value × Ix.Ixby.Value))
  let runCase (id : Nat) (args : Array Ix.Ixby.Value) (expected : Ix.Ixby.Value) : IO Unit := do
    let actual ← execute { image.program with entry := id } args
    need (actual == expected) s!"word helper {id}: {reprStr args}: expected {reprStr expected}, got {reprStr actual}"
    if let .ctor _ _ := expected then discard <| checked (image.decodeNumber actual)
    let old := (← registered.get)[id]?.getD 0
    if old < 3 then
      registered.modify (·.insert id (old + 1))
      callerCases.modify (·.push (id, args, expected))
    count.modify (· + 1)
  let numbers := #[0, 1, 2, 127, 128, 255, 256, 257, 65535, 65536, 2 ^ 31 - 1, 2 ^ 31,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, Ix.Ixby.goldilocksModulus - 1, Ix.Ixby.goldilocksModulus,
    Ix.Ixby.goldilocksModulus + 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 80 + 17, 2 ^ 256 + 255]
  for n in numbers do
    for (n, value) in cases n do
      runCase links.u8OfNat #[value] (cached n.toUInt8.toNat)
      runCase links.u32OfNat #[value] (cached n.toUInt32.toNat)
      runCase links.usizeOfNat #[value] (cached n.toUSize.toNat)
  for n in #[0, 1, 255, 256, 2 ^ 16, 2 ^ 31, 2 ^ 32 - 1] do
    for (n, value) in cases n do
      for proofValue in #[Ix.Ixby.Value.erased, .scalar (.word32 0xC0FFEE), raw 123] do
        runCase links.u32OfNatLT #[value, proofValue] (cached n)
  let u8Binary : Array (Nat × (UInt8 → UInt8 → Ix.Ixby.Value)) := #[
    (links.u8Add, fun a b => cached (a + b).toNat),
    (links.u8Equal, fun a b => .scalar (.bool (a == b))),
    (links.u8ShiftLeft, fun a b => cached (a <<< b).toNat),
    (links.u8ShiftRight, fun a b => cached (a >>> b).toNat)]
  for n in Array.range 256 do
    for (_, value) in cases n do
      runCase links.u8ToNat #[value] value
      runCase links.u8ToU32 #[value] value
    for amount in #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 31, 32, 255] do
      for (id, source) in u8Binary do
        runCase id #[cached n, cached amount] (source n.toUInt8 amount.toUInt8)
  for a in #[0, 1, 2, 7, 8, 127, 128, 255] do
    for b in #[0, 1, 7, 8, 31, 32, 128, 255] do
      for (a, left) in cases a do
        for (b, right) in cases b do
          for (id, source) in u8Binary do
            runCase id #[left, right] (source a.toUInt8 b.toUInt8)
  let u32Binary : Array (Nat × (UInt32 → UInt32 → Ix.Ixby.Value)) := #[
    (links.u32Add, fun a b => cached (a + b).toNat),
    (links.u32Sub, fun a b => cached (a - b).toNat),
    (links.u32Mul, fun a b => cached (a * b).toNat),
    (links.u32And, fun a b => cached (a &&& b).toNat),
    (links.u32Or, fun a b => cached (a ||| b).toNat),
    (links.u32Xor, fun a b => cached (a ^^^ b).toNat),
    (links.u32ShiftLeft, fun a b => cached (a <<< b).toNat),
    (links.u32ShiftRight, fun a b => cached (a >>> b).toNat),
    (links.u32Equal, fun a b => .scalar (.bool (a == b))),
    (links.u32Less, fun a b => .scalar (.bool (a < b)))]
  let wordNumbers := #[0, 1, 2, 7, 8, 31, 32, 33, 127, 128, 255, 256, 65535, 65536, 2 ^ 31, 2 ^ 32 - 1]
  for a in wordNumbers do
    for (a, value) in cases a do
      runCase links.u32ToNat #[value] value
      runCase links.u32ToU8 #[value] (cached a.toUInt32.toUInt8.toNat)
    for b in wordNumbers do
      for (a, left) in cases a do
        for (b, right) in cases b do
          for (id, source) in u32Binary do
            runCase id #[left, right] (source a.toUInt32 b.toUInt32)
  let usizeBinary : Array (Nat × (USize → USize → Ix.Ixby.Value)) := #[
    (links.usizeAdd, fun a b => cached (a + b).toNat),
    (links.usizeSub, fun a b => cached (a - b).toNat),
    (links.usizeEqual, fun a b => .scalar (.bool (a == b))),
    (links.usizeLess, fun a b => .scalar (.bool (a < b)))]
  let sizeNumbers := #[0, 1, 2, 255, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, Ix.Ixby.goldilocksModulus - 1,
    Ix.Ixby.goldilocksModulus, Ix.Ixby.goldilocksModulus + 1, 2 ^ 63, 2 ^ 64 - 1]
  for a in sizeNumbers do
    for (_, value) in cases a do runCase links.usizeToNat #[value] value
    for b in sizeNumbers do
      for (a, left) in cases a do
        for (b, right) in cases b do
          for (id, source) in usizeBinary do
            runCase id #[left, right] (source a.toUSize b.toUSize)
  need ((← registered.get).size == 27) "word execution suite missed a generated helper"
  let large := 2 ^ 256 + 255
  for (id, expected) in #[(links.u8OfNat, large.toUInt8.toNat),
      (links.u32OfNat, large.toUInt32.toNat), (links.usizeOfNat, large.toUSize.toNat)] do
    callerCases.modify (·.push (id, #[raw large], cached expected))
  callerCases.modify (·.push (links.u32OfNatLT, #[raw (2 ^ 32 - 1), .erased], cached (2 ^ 32 - 1)))
  callerCases.modify (·.push (links.u32ToU8, #[raw (2 ^ 32 - 1)], cached 255))
  for (id, value) in #[(links.u8ToNat, raw 255), (links.u8ToU32, field 255),
      (links.u32ToNat, raw (2 ^ 32 - 1)), (links.usizeToNat, raw (2 ^ 64 - 1))] do
    callerCases.modify (·.push (id, #[value], value))
  for (id, source) in u8Binary do
    callerCases.modify (·.push (id, #[raw 255, field 255], source 255 255))
  for (a, b) in #[(2 ^ 32 - 1, 255), (0, 1), (2 ^ 32 - 1, 32)] do
    for (id, source) in u32Binary do
      callerCases.modify (·.push (id, #[raw a, field b], source a.toUInt32 b.toUInt32))
  for (a, b) in #[(2 ^ 64 - 1, 1), (0, 2 ^ 64 - 1), (Ix.Ixby.goldilocksModulus - 1, 3)] do
    for (id, source) in usizeBinary do
      callerCases.modify (·.push (id, #[raw a, raw b], source a.toUSize b.toUSize))
  let callerCount ← IO.mkRef 0
  for (id, args, expected) in ← callerCases.get do
    let allArgs := args.push (.scalar (.word32 0xC0FFEE))
    let mut blocks : Array Ix.Ixby.Block := #[⟨allArgs.size,
      .letOp (.call id ((List.range args.size).map Ix.Ixby.Operand.local)) 1⟩]
    let mut result := allArgs.size
    let mut locals := allArgs.size + 1
    let mut expected := expected
    for i in (List.range allArgs.size).reverse do
      blocks := blocks.push ⟨locals, .letOp (.construct links.conversions.cachedCtor
        [.local i, .local result]) (blocks.size + 1)⟩
      result := locals
      locals := locals + 1
      expected := .ctor layout.cached #[allArgs[i]!, expected]
    blocks := blocks.push ⟨locals, .ret (.local result)⟩
    let caller : Ix.Ixby.Function := { arity := allArgs.size, blocks }
    let actual ← execute { image.program with
      entry := image.program.functions.size
      functions := image.program.functions.push caller } allArgs
    need (actual == expected) s!"word caller {id} lost an input, proof slot, sentinel, or result"
    callerCount.modify (· + 1)
  let localCount ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 200000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"word resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    localCount.modify (· + 1)
  let identityOnly : Ix.Ixby.Limits := {
    image.state.limits with locals := 1, continuations := 0, natBits := 0, byteArrayBytes := 0 }
  for id in #[links.u8ToNat, links.u8ToU32, links.u32ToNat, links.usizeToNat] do
    localRun identityOnly id #[cached 255] (.ok (cached 255))
    localRun { identityOnly with locals := 0 } id #[cached 255] (.error (.limit .locals))
  let observed : Ix.Ixby.Limits := {
    image.state.limits with locals := 11, continuations := 3, natBits := 64, byteArrayBytes := 8 }
  let maxField := Ix.Ixby.goldilocksModulus - 1
  localRun observed links.usizeEqual #[field maxField, raw maxField] (.ok (.scalar (.bool true)))
  localRun { observed with locals := 9 } links.usizeEqual #[field maxField, raw maxField]
    (.error (.limit .locals))
  localRun { observed with continuations := 2 } links.usizeEqual #[field maxField, raw maxField]
    (.error (.limit .continuations))
  localRun { observed with byteArrayBytes := 7 } links.usizeEqual #[field maxField, raw maxField]
    (.error (.limit .byteArrayBytes))
  localRun { observed with natBits := 63 } links.usizeEqual #[field maxField, raw maxField]
    (.error (.limit .natBits))
  localRun observed links.u8OfNat #[field maxField] (.ok (cached maxField.toUInt8.toNat))
  localRun { observed with locals := 10 } links.u8OfNat #[raw 65535] (.error (.limit .locals))
  localRun { observed with natBits := 32 } links.u32OfNat #[cached 0] (.error (.limit .natBits))
  localRun { observed with natBits := 33 } links.u32OfNat #[cached 0] (.ok (cached 0))
  localRun observed links.usizeOfNat #[cached 0] (.error (.limit .natBits))
  localRun { observed with natBits := 65 } links.usizeOfNat #[cached 0] (.ok (cached 0))
  localRun { observed with natBits := 257 } links.u32OfNat #[raw (2 ^ 256 + 255)] (.ok (cached 255))
  localRun { observed with natBits := 256 } links.u32OfNat #[raw (2 ^ 256 + 255)] (.error (.limit .natBits))
  let modular := { observed with locals := 14 }
  localRun modular links.u8Add #[raw 255, field 1] (.ok (cached 0))
  localRun { modular with locals := 13 } links.u8Add #[cached 255, cached 1] (.error (.limit .locals))
  localRun { modular with locals := 13 } links.u32Add #[cached (2 ^ 32 - 1), cached 1] (.ok (cached 0))
  localRun { modular with locals := 12 } links.u32Add #[cached (2 ^ 32 - 1), cached 1] (.error (.limit .locals))
  localRun modular links.u32Mul #[cached (2 ^ 32 - 1), cached (2 ^ 32 - 1)] (.ok (cached 1))
  localRun { modular with natBits := 63 } links.u32Mul #[cached (2 ^ 32 - 1), cached (2 ^ 32 - 1)]
    (.error (.limit .natBits))
  localRun modular links.u32Sub #[cached 0, field 1] (.ok (cached (2 ^ 32 - 1)))
  localRun { modular with locals := 13 } links.u32Sub #[cached 0, cached 1] (.error (.limit .locals))
  localRun modular links.usizeAdd #[cached (2 ^ 64 - 1), cached 1] (.error (.limit .natBits))
  localRun { modular with natBits := 65 } links.usizeAdd #[cached (2 ^ 64 - 1), cached 1] (.ok (cached 0))
  localRun modular links.usizeSub #[cached 0, cached 1] (.error (.limit .natBits))
  localRun { modular with natBits := 65 } links.usizeSub #[cached 0, cached 1] (.ok (cached (2 ^ 64 - 1)))
  localRun { modular with natBits := 65 } links.usizeSub #[field maxField, raw maxField] (.ok (cached 0))
  let logical := { observed with continuations := 2, natBits := 33 }
  localRun logical links.u32And #[raw (2 ^ 32 - 1), field (2 ^ 32 - 1)] (.ok (cached (2 ^ 32 - 1)))
  localRun { logical with locals := 10 } links.u32And #[raw (2 ^ 32 - 1), cached (2 ^ 32 - 1)]
    (.error (.limit .locals))
  localRun { logical with continuations := 1 } links.u32Or #[cached (2 ^ 32 - 1), cached 0]
    (.error (.limit .continuations))
  localRun { logical with byteArrayBytes := 7 } links.u32Xor #[field 1, cached 1]
    (.error (.limit .byteArrayBytes))
  localRun { logical with natBits := 32 } links.u32Or #[cached (2 ^ 32 - 1), cached 0]
    (.error (.limit .natBits))
  localRun logical links.u32ShiftLeft #[field 1, raw 31] (.ok (cached (2 ^ 31)))
  localRun logical links.u32ShiftLeft #[field 1, raw 32] (.ok (cached 1))
  localRun logical links.u32ShiftRight #[raw (2 ^ 32 - 1), field 255] (.ok (cached 1))
  localRun logical links.u8ShiftLeft #[raw 255, field 8] (.ok (cached 255))
  localRun logical links.u8ShiftLeft #[raw 255, field 7] (.ok (cached 128))
  localRun logical links.u8ShiftRight #[field 255, raw 255] (.ok (cached 1))
  IO.println s!"check-ixby-lean word contracts: {← count.get} admitted executions; {← callerCount.get} caller cases; {← localCount.get} resource cases"
private def arrayTreeEncode (layout : Compilatrix.Ixby.Runtime.ArrayTrees.Layout)
    (height offset : Nat) (slots : Array (Option Ix.Ixby.Value)) : Ix.Ixby.Value :=
  if (slots.extract offset (offset + 2 ^ height)).all Option.isNone then
    .ctor layout.empty #[]
  else match height with
    | 0 => match slots[offset]?.getD none with
      | some value => .ctor layout.leaf #[value]
      | none => .ctor layout.empty #[]
    | height + 1 => .ctor layout.node #[arrayTreeEncode layout height offset slots,
        arrayTreeEncode layout height (offset + 2 ^ height) slots]

private def arrayTreeEntries (layout : Compilatrix.Ixby.Runtime.ArrayTrees.Layout)
    (height offset : Nat) (tree : Ix.Ixby.Value) : Except String (Array (Nat × Ix.Ixby.Value)) := do
  if tree == .ctor layout.empty #[] then return #[]
  match height, tree with
  | 0, .ctor tag #[value] =>
    unless tag == layout.leaf do throw "array tree leaf tag"
    return #[(offset, value)]
  | height + 1, .ctor tag #[left, right] =>
    unless tag == layout.node do throw "array tree node tag"
    return (← arrayTreeEntries layout height offset left) ++
      (← arrayTreeEntries layout height (offset + 2 ^ height) right)
  | _, _ => throw "array tree height or field invariant"

private def arrayTreeDecode (image : Image) (layout : Compilatrix.Ixby.Runtime.ArrayTrees.Layout)
    (value : Ix.Ixby.Value) : Except String (Nat × Ix.Ixby.Value × Array (Nat × Ix.Ixby.Value)) := do
  let .ctor tag #[sizeValue, .scalar (.nat capacity), tree] := value | throw "array layout"
  unless tag == layout.array do throw "array tag"
  let size ← image.decodeNumber sizeValue
  unless size ≤ capacity && capacity != 0 && 2 ^ capacity.log2 == capacity do throw "array size/capacity invariant"
  return (size, sizeValue, ← arrayTreeEntries layout capacity.log2 0 tree)

private def arrayTreeSparse (layout : Compilatrix.Ixby.Runtime.ArrayTrees.Layout)
    (height index : Nat) (value : Ix.Ixby.Value) : Ix.Ixby.Value :=
  match height with
  | 0 => .ctor layout.leaf #[value]
  | height + 1 =>
    let empty : Ix.Ixby.Value := .ctor layout.empty #[]
    if index < 2 ^ height then
      .ctor layout.node #[arrayTreeSparse layout height index value, empty]
    else .ctor layout.node #[empty, arrayTreeSparse layout height (index - 2 ^ height) value]

private def arrayTreeMutations (image : Image) : IO Unit := do
  let certified ← checked image.certifyArrayTrees
  let links := certified.links
  let arithmetic := links.arithmetic
  let conversions := arithmetic.conversions
  let instruction (id block : Nat) (changed : Ix.Ixby.Instr) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id fun fn =>
      { fn with blocks := fn.blocks.modify block fun old => { old with instruction := changed } } } }
  let function (id : Nat) (change : Ix.Ixby.Function → Ix.Ixby.Function) : Image :=
    { image with program := { image.program with functions := image.program.functions.modify id change } }
  let rejected ← IO.mkRef 0
  let admittedCount ← IO.mkRef 0
  let reject (changed : Image) (label : String) (admitted := true) : IO Unit := do
    if admitted then
      discard <| checked (Ix.Ixby.validateProgram changed.state.limits changed.program |>.mapError reprStr)
      admittedCount.modify (· + 1)
    match changed.certifyArrayTrees with
    | .error _ => rejected.modify (· + 1)
    | .ok _ => throw (IO.userError s!"array certificate accepted {label}")
  let helpers : Array (Nat × Name) := #[(links.treeGet, `Ixby.Runtime.treeGet),
    (links.treeSet, `Ixby.Runtime.treeSet), (links.size, `Array.size), (links.usize, `Array.usize),
    (links.empty, `Array.emptyWithCapacity), (links.mkEmpty, `Array.mkEmpty),
    (links.get, `Array.getInternal), (links.getBorrowed, `Array.getInternalBorrowed),
    (links.uget, `Array.uget), (links.ugetBorrowed, `Array.ugetBorrowed),
    (links.getBang, `Array.get!Internal), (links.getBangBorrowed, `Array.get!InternalBorrowed),
    (links.push, `Array.push), (links.set, `Array.set!), (links.uset, `Array.uset)]
  for (id, name) in helpers do
    let fn := image.program.functions[id]!
    reject (instruction id (fn.blocks.size - 1) (.ret .erased)) s!"changed return of {name}"
    let functionNames := image.state.functionNames.insert name (if id == links.treeGet then links.size else links.treeGet)
    reject { image with state := { image.state with functionNames } } s!"wrong binding of {name}"
  for id in #[conversions.toWord, conversions.fromWordLoop, conversions.fromWord, conversions.fromRaw,
      conversions.lowWord, conversions.natural, conversions.fieldNatural, conversions.asField,
      conversions.fieldFromNatural, conversions.nibbleWord, conversions.nibbleNat,
      arithmetic.add, arithmetic.sub, arithmetic.mul, arithmetic.div, arithmetic.mod,
      arithmetic.equal, arithmetic.less, arithmetic.lessEqual, links.usizeOfNat] do
    let fn := image.program.functions[id]!
    reject (instruction id (fn.blocks.size - 1) (.ret .erased)) s!"changed numeric dependency {id}"
  for (id, name) in #[(links.emptyCtor, `Ixby.Runtime.Empty), (links.leafCtor, `Ixby.Runtime.Leaf),
      (links.nodeCtor, `Ixby.Runtime.Node), (links.arrayCtor, `Ixby.Runtime.Array),
      (links.bytesCtor, `Ixby.Runtime.Bytes), (links.ropeCtor, `Ixby.Runtime.Rope)] do
    let constructors := image.program.constructors.modify id fun ctor => { ctor with fields := ctor.fields + 1 }
    reject { image with program := { image.program with constructors } } s!"wrong fields of {name}" false
    let constructorNames := image.state.constructorNames.insert name
      (if id == links.arrayCtor then links.bytesCtor else links.arrayCtor)
    reject { image with state := { image.state with constructorNames } } s!"wrong layout name of {name}"
  for (id, tag) in #[(links.nodeCtor, links.layout.empty), (links.arrayCtor, links.layout.bytes),
      (links.ropeCtor, links.layout.bytes), (links.ropeCtor, links.layout.array)] do
    let constructors := image.program.constructors.modify id fun ctor => { ctor with id := tag }
    reject { image with program := { image.program with constructors } } "colliding dispatch tags" false
  reject (instruction links.treeGet 0 (.letOp (.primitive .natEq [.local 1, .literal (.nat 0)]) 1)) "wrong leaf capacity"
  reject (instruction links.treeGet 3 (.letOp (.primitive .natDiv [.local 1, .literal (.nat 3)]) 5)) "wrong tree split"
  reject (instruction links.treeGet 6 (.branch (.local 5) 8 7)) "reversed lookup branch"
  reject (instruction links.treeGet 8 (.letOp (.project (.local 0) 0) 10)) "wrong right child"
  reject (instruction links.treeGet 10 (.letOp (.primitive .natSub [.local 4, .local 2]) 11)) "reversed lookup index"
  reject (instruction links.treeGet 9 (.tailCall links.treeGet [.local 6, .local 4, .local 1])) "wrong recursive lookup index"
  reject (instruction links.treeSet 2 (.letOp (.construct links.leafCtor [.local 0]) 4)) "stored old tree instead of item"
  reject (instruction links.treeSet 3 (.letOp (.primitive .natDiv [.local 1, .literal (.nat 4)]) 5)) "wrong update split"
  reject (instruction links.treeSet 9 (.branch (.local 7) 11 10)) "reversed sparse update branch"
  reject (instruction links.treeSet 11 (.letOp (.primitive .natSub [.local 5, .local 2]) 14)) "reversed sparse update index"
  reject (instruction links.treeSet 12 (.letOp (.construct links.nodeCtor [.local 6, .local 8]) 13)) "swapped sparse update children"
  reject (instruction links.treeSet 20 (.letOp (.construct links.nodeCtor [.local 9, .local 6]) 21)) "lost untouched right subtree"
  reject (instruction links.treeSet 23 (.letOp (.construct links.nodeCtor [.local 10, .local 6]) 24)) "swapped updated right subtree"
  reject (instruction links.size 2 (.ret (.local 3))) "returned capacity as size"
  reject (instruction links.usize 1 (.tailCall conversions.fromRaw [.local 2])) "wrong USize adapter"
  reject (instruction links.empty 2 (.letOp (.construct links.arrayCtor [.local 2, .literal (.nat 0), .local 3]) 3)) "zero array capacity"
  reject (instruction links.mkEmpty 0 (.letOp (.construct conversions.cachedCtor [.literal (.nat 0), .literal (.word32 1)]) 1)) "inconsistent empty size cache"
  reject (instruction links.get 1 (.letOp (.call arithmetic.less [.local 4, .local 2]) 2)) "reversed array bounds"
  reject (instruction links.get 2 (.branch (.local 5) 4 3)) "reversed checked lookup"
  reject (instruction links.get 6 (.letOp (.call conversions.natural [.local 3]) 10)) "observed lookup proof slot"
  reject (instruction links.getBorrowed 0 (.tailCall links.get [.erased, .local 1, .local 0, .erased])) "wrong borrowed index"
  reject (instruction links.getBang 4 (.ret (.local 0))) "wrong default value"
  reject (instruction links.getBangBorrowed 3 (.tailCall links.get [.erased, .local 2, .local 1, .erased])) "default used as index"
  reject (instruction links.push 2 (.letOp (.call arithmetic.sub [.local 3, .local 4]) 3)) "decremented push size"
  reject (instruction links.push 11 (.letOp (.primitive .natMul [.local 7, .local 7]) 14)) "squared growth capacity"
  reject (instruction links.push 15 (.letOp (.construct links.nodeCtor [.local 12, .local 8]) 16)) "reversed growth children"
  reject (instruction links.push 16 (.letOp (.call links.treeSet [.local 8, .local 11, .local 9, .local 2]) 17)) "wrote old root at larger capacity"
  reject (instruction links.push 17 (.letOp (.construct links.arrayCtor [.local 3, .local 11, .local 14]) 18)) "retained old push size"
  reject (instruction links.set 4 (.ret (.local 3))) "returned item for out-of-bounds set"
  reject (instruction links.set 10 (.letOp (.construct links.arrayCtor [.local 4, .local 7, .local 8]) 11)) "discarded updated root"
  reject (instruction links.uset 1 (.letOp (.call arithmetic.less [.local 4, .local 5]) 2)) "used update proof as index"
  reject (function links.treeSet fun fn => { fn with blocks := fn.blocks.push ⟨0, .ret .erased⟩ }) "extra unreachable tree block"
  reject (function links.treeGet fun fn => { fn with entry := 1000 }) "missing tree entry" false
  reject (function links.uset fun fn => { fn with arity := 4 }) "omitted update proof slot" false
  let functionNames := image.state.functionNames.insert `Ixby.Runtime.treeSet (image.program.functions.size + 1)
  reject { image with state := { image.state with functionNames } } "missing tree function candidate"
  -- The certificate's scope is the tree branches. Byte callback bodies remain
  -- separate obligations, while their names/indices are pinned by exact code.
  let bytesChanged := instruction links.byteGet 0 (.ret .erased)
  discard <| checked bytesChanged.certifyArrayTrees
  IO.println s!"check-ixby-lean arrays: 15 generated functions; {← rejected.get} rejected mutations ({← admittedCount.get} structurally admitted)"

private def arrayTreeExecutions (image : Image) : IO Unit := do
  need (System.Platform.numBits == 64) "array usize source oracle requires the compiler's 64-bit platform"
  let certified ← checked image.certifyArrayTrees
  let links := certified.links
  let layout := links.layout
  let numbers := links.arithmetic.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value := .ctor numbers.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor numbers.raw #[.scalar (.nat n)]
  let field (n : Nat) : Ix.Ixby.Value := .ctor numbers.field #[.scalar (.field (Ix.Ixby.Goldilocks.reduce n))]
  let cases (n : Nat) : Array (Nat × Ix.Ixby.Value) :=
    #[(n, cached n), (n, raw n), (n % Ix.Ixby.goldilocksModulus, field n)]
  let array (height : Nat) (size tree : Ix.Ixby.Value) : Ix.Ixby.Value :=
    .ctor layout.array #[size, .scalar (.nat (2 ^ height)), tree]
  let entries (source : Array Ix.Ixby.Value) : Array (Nat × Ix.Ixby.Value) :=
    (Array.range source.size).map fun i => (i, source[i]!)
  let pool : Array Ix.Ixby.Value := #[.erased, .scalar (.word32 0xC0FFEE), .scalar (.bool true),
    raw (2 ^ 256 + 17), cached (2 ^ 32 + 7), field (Ix.Ixby.goldilocksModulus - 1),
    .ctor layout.node #[.scalar (.str "array element"), .scalar (.bytes #[0, 255, 19])],
    .pap links.arithmetic.add #[cached 3]]
  let typeValue := pool[7]!
  let proofValue := pool[6]!
  let fallback := pool[1]!
  let count ← IO.mkRef 0
  let negativeCount ← IO.mkRef 0
  let registered ← IO.mkRef ({} : Std.HashMap Nat Nat)
  let callerCases ← IO.mkRef (#[] : Array (Nat × Array Ix.Ixby.Value × Ix.Ixby.Value))
  let execute (program : Ix.Ixby.Program) (args : Array Ix.Ixby.Value) : IO Ix.Ixby.Value := do
    discard <| checked (Compilatrix.Ixby.Runtime.ArrayTrees.certify program links)
    checked (Ix.Ixby.execute image.state.limits program args 200000 |>.mapError reprStr)
  let runCase (id : Nat) (args : Array Ix.Ixby.Value) (checkResult : Ix.Ixby.Value → IO Unit) : IO Ix.Ixby.Value := do
    let actual ← execute { image.program with entry := id } args
    checkResult actual
    let old := (← registered.get)[id]?.getD 0
    if old < 3 then
      registered.modify (·.insert id (old + 1))
      callerCases.modify (·.push (id, args, actual))
    count.modify (· + 1)
    return actual
  let exactValue (expected actual : Ix.Ixby.Value) : IO Unit :=
    need (actual == expected) s!"array exact result: expected {reprStr expected}, got {reprStr actual}"
  let treeResult (height : Nat) (expected : Array (Nat × Ix.Ixby.Value)) (actual : Ix.Ixby.Value) : IO Unit := do
    let got ← checked (arrayTreeEntries layout height 0 actual)
    need (got == expected) s!"tree slots at height {height}: expected {reprStr expected}, got {reprStr got}"
  let arrayResult (source : Array Ix.Ixby.Value) (actual : Ix.Ixby.Value) : IO Unit := do
    let (size, _, got) ← checked (arrayTreeDecode image layout actual)
    need (size == source.size && got == entries source)
      s!"source array mismatch: expected {reprStr source}, got length {size} with {reprStr got}"
  let rejectCase (id : Nat) (args : Array Ix.Ixby.Value) (expected : Ix.Ixby.Error) : IO Unit := do
    let program := { image.program with entry := id }
    discard <| checked (Compilatrix.Ixby.Runtime.ArrayTrees.certify program links)
    discard <| checked (Ix.Ixby.validateProgram image.state.limits program |>.mapError reprStr)
    discard <| checked (Ix.Ixby.validateInputValues image.state.limits program image.state.limits.inputNodes args.toList |>.mapError reprStr)
    match Ix.Ixby.execute image.state.limits program args 200000 with
    | .error actual => need (actual == expected) s!"array rejection {id}: {reprStr actual}"
    | .ok actual => throw (IO.userError s!"array rejection {id} returned {reprStr actual}")
    negativeCount.modify (· + 1)
  let empty := .ctor layout.empty #[]
  for requested in #[0, 1, 2, 31, 32, 2 ^ 32, 2 ^ 64, 2 ^ 256 + 1] do
    for (_, capValue) in cases requested do
      for id in #[links.empty, links.mkEmpty] do
        discard <| runCase id #[typeValue, capValue] (exactValue (array 0 (cached 0) empty))
  for capValue in #[Ix.Ixby.Value.erased, proofValue, typeValue] do
    for id in #[links.empty, links.mkEmpty] do
      discard <| runCase id #[typeValue, capValue] (exactValue (array 0 (cached 0) empty))
  for height in Array.range 6 do
    let capacity := 2 ^ height
    for n in Array.range (capacity + 1) do
      let source := (Array.range n).map fun i => pool[(i + n) % pool.size]!
      let slots := (Array.range capacity).map fun i => source[i]?
      let tree := arrayTreeEncode layout height 0 slots
      for index in Array.range n do
        discard <| runCase links.treeGet #[tree, .scalar (.nat capacity), .scalar (.nat index)]
          (exactValue source[index]!)
      for index in Array.range capacity do
        let replacement := pool[(index + n + 3) % pool.size]!
        let changed := slots.set! index (some replacement)
        let expected := (Array.range capacity).filterMap fun i => changed[i]!.map fun value => (i, value)
        discard <| runCase links.treeSet #[tree, .scalar (.nat capacity), .scalar (.nat index), replacement]
          (treeResult height expected)
      for (_, sizeValue) in cases n do
        let input := array height sizeValue tree
        discard <| runCase links.size #[typeValue, input] (exactValue sizeValue)
        discard <| runCase links.usize #[typeValue, input] (exactValue (cached source.usize.toNat))
        for replacement in pool do
          let output ← runCase links.push #[typeValue, input, replacement] (arrayResult (source.push replacement))
          let (_, nextSize, _) ← checked (arrayTreeDecode image layout output)
          need (nextSize == (if sizeValue == cached n then cached (n + 1) else raw (n + 1)))
            "push size representation or cache changed"
        for index in Array.range n do
          for (_, indexValue) in cases index do
            for id in #[links.get, links.getBorrowed, links.uget, links.ugetBorrowed] do
              discard <| runCase id #[typeValue, input, indexValue, proofValue] (exactValue source[index]!)
            for id in #[links.getBang, links.getBangBorrowed] do
              discard <| runCase id #[typeValue, fallback, input, indexValue] (exactValue (source.getD index fallback))
            let replacement := pool[(index + n + 5) % pool.size]!
            discard <| runCase links.set #[typeValue, input, indexValue, replacement]
              (arrayResult (source.set! index replacement))
            discard <| runCase links.uset #[typeValue, input, indexValue, replacement, proofValue]
              (arrayResult (source.set! index replacement))
        for index in #[n, n + 1, capacity + 1, 2 ^ 32, 2 ^ 64 + 17, 2 ^ 256 + 3] do
          for (observedIndex, indexValue) in cases index do
            -- Canonical field representations expose their own exact Nat.
            if observedIndex ≥ n then
              for id in #[links.get, links.getBorrowed, links.uget, links.ugetBorrowed] do
                rejectCase id #[typeValue, input, indexValue, proofValue] .notConstructor
              rejectCase links.uset #[typeValue, input, indexValue, pool[2]!, proofValue] .notConstructor
              for id in #[links.getBang, links.getBangBorrowed] do
                discard <| runCase id #[typeValue, fallback, input, indexValue] (exactValue fallback)
              discard <| runCase links.set #[typeValue, input, indexValue, pool[2]!] (exactValue input)
  -- Noncanonical unused subtrees and dead slots are preserved by updates.
  let materialized := .ctor layout.node #[.ctor layout.empty #[], .ctor layout.empty #[]]
  let noncanonical := .ctor layout.node #[materialized, materialized]
  let kept ← runCase links.treeSet #[noncanonical, .scalar (.nat 4), .scalar (.nat 0), pool[7]!]
    (treeResult 2 #[(0, pool[7]!)])
  need (kept == .ctor layout.node #[.ctor layout.node #[.ctor layout.leaf #[pool[7]!], empty], materialized])
    "tree write discarded an untouched materialized empty subtree"
  let deadSlots : Array (Option Ix.Ixby.Value) := #[some pool[0]!, none, none, none, none, some pool[7]!, none, none]
  let deadTree := arrayTreeEncode layout 3 0 deadSlots
  let deadArray := array 3 (field 1) deadTree
  let deadPushed ← runCase links.push #[typeValue, deadArray, pool[6]!] fun actual => do
    let (size, _, got) ← checked (arrayTreeDecode image layout actual)
    need (size == 2 && got == #[(0, pool[0]!), (1, pool[6]!), (5, pool[7]!)]) "push corrupted dead slots"
  callerCases.modify (·.push (links.push, #[typeValue, deadArray, pool[6]!], deadPushed))
  -- Deep sparse trees exercise capacities and indices far above machine words
  -- without allocating an array with that many unused slots.
  for height in #[7, 8, 16, 31, 32, 63, 64, 80, 128, 256] do
    let capacity := 2 ^ height
    for index in #[0, 1, capacity / 2 - 1, capacity / 2, capacity - 1] do
      let value := pool[(height + index) % pool.size]!
      let written ← runCase links.treeSet #[empty, .scalar (.nat capacity), .scalar (.nat index), value]
        (treeResult height #[(index, value)])
      discard <| runCase links.treeGet #[written, .scalar (.nat capacity), .scalar (.nat index)] (exactValue value)
      callerCases.modify (·.push (links.treeSet, #[empty, .scalar (.nat capacity), .scalar (.nat index), value], written))
    let firstTree := arrayTreeSparse layout height 0 pool[7]!
    let source := #[pool[7]!]
    for (_, sizeValue) in cases 1 do
      let input := array height sizeValue firstTree
      discard <| runCase links.push #[typeValue, input, pool[6]!] (arrayResult (source.push pool[6]!))
      for (_, indexValue) in cases 0 do
        discard <| runCase links.get #[typeValue, input, indexValue, proofValue] (exactValue pool[7]!)
        let output ← runCase links.set #[typeValue, input, indexValue, pool[5]!]
          (arrayResult (source.set! 0 pool[5]!))
        callerCases.modify (·.push (links.set, #[typeValue, input, indexValue, pool[5]!], output))
  -- Feed actual returned arrays into later operations through several growth
  -- boundaries, maintaining an independent ordinary Array oracle.
  let mut source : Array Ix.Ixby.Value := #[]
  let mut current ← runCase links.mkEmpty #[typeValue, raw 1000] (arrayResult source)
  for i in Array.range 257 do
    let item := pool[i % pool.size]!
    source := source.push item
    current ← runCase links.push #[typeValue, current, item] (arrayResult source)
    let index := (i * 17 + 3) % source.size
    let replacement := pool[(i + 3) % pool.size]!
    source := source.set! index replacement
    current ← runCase links.set #[typeValue, current, field index, replacement] (arrayResult source)
    discard <| runCase links.getBorrowed #[typeValue, current, raw index, proofValue] (exactValue source[index]!)
  need ((← registered.get).size == 15) "array execution suite missed a generated helper"
  -- Explicit nonzero callers cover every public entry in addition to the
  -- first three cases, so empty arrays cannot hide frame-restoration defects.
  let sampleSource := pool.extract 0 4
  let sampleTree := arrayTreeEncode layout 2 0 (sampleSource.map some)
  let sample := array 2 (field 4) sampleTree
  let retain (id : Nat) (args : Array Ix.Ixby.Value) (checkResult : Ix.Ixby.Value → IO Unit) : IO Unit := do
    let output ← runCase id args checkResult
    callerCases.modify (·.push (id, args, output))
  retain links.treeGet #[sampleTree, .scalar (.nat 4), .scalar (.nat 3)] (exactValue sampleSource[3]!)
  retain links.treeSet #[sampleTree, .scalar (.nat 4), .scalar (.nat 3), pool[7]!]
    (treeResult 2 (entries (sampleSource.set! 3 pool[7]!)))
  retain links.size #[typeValue, sample] (exactValue (field 4))
  retain links.usize #[typeValue, sample] (exactValue (cached 4))
  for id in #[links.empty, links.mkEmpty] do retain id #[typeValue, raw (2 ^ 256 + 1)] (arrayResult #[])
  for id in #[links.get, links.getBorrowed, links.uget, links.ugetBorrowed] do
    retain id #[typeValue, sample, field 3, proofValue] (exactValue sampleSource[3]!)
  for id in #[links.getBang, links.getBangBorrowed] do
    retain id #[typeValue, fallback, sample, raw 3] (exactValue sampleSource[3]!)
    retain id #[typeValue, fallback, sample, raw (2 ^ 256)] (exactValue fallback)
  retain links.push #[typeValue, sample, pool[7]!] (arrayResult (sampleSource.push pool[7]!))
  retain links.set #[typeValue, sample, field 3, pool[7]!] (arrayResult (sampleSource.set! 3 pool[7]!))
  retain links.uset #[typeValue, sample, raw 3, pool[7]!, proofValue] (arrayResult (sampleSource.set! 3 pool[7]!))
  let callerCount ← IO.mkRef 0
  for (id, args, expected) in ← callerCases.get do
    let allArgs := args.push (.scalar (.word32 0xDEADBEEF))
    let mut blocks : Array Ix.Ixby.Block := #[⟨allArgs.size,
      .letOp (.call id ((List.range args.size).map Ix.Ixby.Operand.local)) 1⟩]
    let mut result := allArgs.size
    let mut locals := allArgs.size + 1
    let mut expected := expected
    for i in (List.range allArgs.size).reverse do
      blocks := blocks.push ⟨locals, .letOp (.construct links.nodeCtor
        [.local i, .local result]) (blocks.size + 1)⟩
      result := locals
      locals := locals + 1
      expected := .ctor layout.node #[allArgs[i]!, expected]
    blocks := blocks.push ⟨locals, .ret (.local result)⟩
    let caller : Ix.Ixby.Function := { arity := allArgs.size, blocks }
    let actual ← execute { image.program with
      entry := image.program.functions.size
      functions := image.program.functions.push caller } allArgs
    need (actual == expected) s!"array caller {id} lost an argument, proof slot, sentinel, subtree, or result"
    callerCount.modify (· + 1)
  IO.println s!"check-ixby-lean array contracts: {← count.get} admitted executions; {← negativeCount.get} admitted bounds rejections; {← callerCount.get} caller cases"

private def arrayTreeResources (image : Image) : IO Unit := do
  let certified ← checked image.certifyArrayTrees
  let links := certified.links
  let layout := links.layout
  let numbers := links.arithmetic.conversions.layout
  let cached (n : Nat) : Ix.Ixby.Value := .ctor numbers.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]
  let raw (n : Nat) : Ix.Ixby.Value := .ctor numbers.raw #[.scalar (.nat n)]
  let field (n : Nat) : Ix.Ixby.Value := .ctor numbers.field #[.scalar (.field (Ix.Ixby.Goldilocks.reduce n))]
  let array (height : Nat) (size tree : Ix.Ixby.Value) : Ix.Ixby.Value :=
    .ctor layout.array #[size, .scalar (.nat (2 ^ height)), tree]
  let empty : Ix.Ixby.Value := .ctor layout.empty #[]
  let leaf : Ix.Ixby.Value := .ctor layout.leaf #[.scalar (.word32 99)]
  let values := (Array.range 8).map fun i => Ix.Ixby.Value.scalar (.word32 i.toUInt32)
  let fullTree := arrayTreeEncode layout 3 0 (values.map some)
  let full := array 3 (cached 8) fullTree
  let spareTree := arrayTreeEncode layout 3 0 ((values.extract 0 7).map some)
  let spare := array 3 (cached 7) spareTree
  let item : Ix.Ixby.Value := .pap links.arithmetic.add #[cached 17]
  let count ← IO.mkRef 0
  let localRun (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (expected : Except Ix.Ixby.Error Ix.Ixby.Value) : IO Unit := do
    let actual := Ix.Ixby.run limits image.program 200000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args)
    let same := match actual, expected with
      | .ok actual, .ok expected => actual == expected
      | .error actual, .error expected => actual == expected
      | _, _ => false
    need same s!"array resource contract {id}: expected {reprStr expected}, got {reprStr actual}"
    count.modify (· + 1)
  let localChecked (limits : Ix.Ixby.Limits) (id : Nat) (args : Array Ix.Ixby.Value)
      (source : Array Ix.Ixby.Value) : IO Unit := do
    let actual ← checked (Ix.Ixby.run limits image.program 200000
      (Compilatrix.Ixby.Runtime.ScalarFunction.start id args) |>.mapError reprStr)
    let (size, _, got) ← checked (arrayTreeDecode image layout actual)
    let expected := (Array.range source.size).map fun i => (i, source[i]!)
    need (size == source.size && got == expected) "array resource source result"
    count.modify (· + 1)
  let tiny : Ix.Ixby.Limits := { image.state.limits with
    locals := 5, continuations := 0, natBits := 0, byteArrayBytes := 0 }
  for id in #[links.empty, links.mkEmpty] do
    localRun tiny id #[.erased, item] (.ok (array 0 (cached 0) empty))
    localRun { tiny with locals := 4 } id #[.erased, item] (.error (.limit .locals))
  localRun tiny links.size #[.erased, array 80 (raw 1) empty] (.ok (raw 1))
  localRun { tiny with locals := 4 } links.size #[.erased, full] (.error (.limit .locals))
  let readTree : Ix.Ixby.Limits := { tiny with locals := 8, natBits := 4 }
  localRun readTree links.treeGet #[fullTree, .scalar (.nat 8), .scalar (.nat 7)] (.ok values[7]!)
  localRun { readTree with locals := 7 } links.treeGet #[fullTree, .scalar (.nat 8), .scalar (.nat 7)]
    (.error (.limit .locals))
  localRun { readTree with natBits := 3 } links.treeGet #[fullTree, .scalar (.nat 8), .scalar (.nat 7)]
    (.error (.limit .natBits))
  localRun { readTree with locals := 5, natBits := 1 } links.treeGet #[leaf, .scalar (.nat 1), .scalar (.nat 0)]
    (.ok (.scalar (.word32 99)))
  localRun { readTree with natBits := 0 } links.treeGet #[leaf, .scalar (.nat 1), .scalar (.nat 0)]
    (.error (.limit .natBits))
  let writeTree : Ix.Ixby.Limits := { readTree with locals := 12, continuations := 3 }
  let updated := arrayTreeEncode layout 3 0 ((values.set! 7 item).map some)
  localRun writeTree links.treeSet #[fullTree, .scalar (.nat 8), .scalar (.nat 7), item] (.ok updated)
  localRun { writeTree with locals := 11 } links.treeSet #[fullTree, .scalar (.nat 8), .scalar (.nat 7), item]
    (.error (.limit .locals))
  localRun { writeTree with continuations := 2 } links.treeSet #[fullTree, .scalar (.nat 8), .scalar (.nat 7), item]
    (.error (.limit .continuations))
  localRun { writeTree with locals := 11 } links.treeSet #[empty, .scalar (.nat 8), .scalar (.nat 7), item]
    (.ok (arrayTreeSparse layout 3 7 item))
  localRun { tiny with locals := 6, natBits := 1 } links.treeSet #[empty, .scalar (.nat 1), .scalar (.nat 0), item]
    (.ok (.ctor layout.leaf #[item]))
  let observed : Ix.Ixby.Limits := { image.state.limits with
    locals := 10, continuations := 4, natBits := 64, byteArrayBytes := 8 }
  let fieldArray := array 3 (field 8) fullTree
  for id in #[links.get, links.getBorrowed, links.uget, links.ugetBorrowed] do
    localRun observed id #[.erased, fieldArray, field 7, item] (.ok values[7]!)
  localRun { observed with locals := 9 } links.get #[.erased, fieldArray, field 7, item] (.error (.limit .locals))
  localRun { observed with continuations := 3 } links.get #[.erased, fieldArray, field 7, item] (.error (.limit .continuations))
  localRun { observed with byteArrayBytes := 7 } links.get #[.erased, fieldArray, field 7, item] (.error (.limit .byteArrayBytes))
  localRun observed links.get #[.erased, fieldArray, raw 8, item] (.error .notConstructor)
  localRun observed links.uset #[.erased, fieldArray, raw 8, item, .erased] (.error .notConstructor)
  localRun observed links.getBang #[.erased, item, fieldArray, raw 8] (.ok item)
  localRun observed links.set #[.erased, fieldArray, raw 8, item] (.ok fieldArray)

  let usize := { observed with locals := 11, continuations := 3, natBits := 65 }
  localRun usize links.usize #[.erased, fieldArray] (.ok (cached 8))
  localRun { usize with natBits := 64 } links.usize #[.erased, fieldArray] (.error (.limit .natBits))
  localRun { usize with continuations := 2 } links.usize #[.erased, fieldArray] (.error (.limit .continuations))
  localRun { usize with byteArrayBytes := 7 } links.usize #[.erased, fieldArray] (.error (.limit .byteArrayBytes))
  -- Exact tree capacity, rather than the small selected index/result, controls
  -- these primitive Nat failures.
  for height in #[32, 63, 64, 256] do
    let tree := arrayTreeSparse layout height 0 item
    let capacity := 2 ^ height
    let enough := { readTree with natBits := height + 1 }
    localRun enough links.treeGet #[tree, .scalar (.nat capacity), .scalar (.nat 0)] (.ok item)
    localRun { enough with natBits := height } links.treeGet #[tree, .scalar (.nat capacity), .scalar (.nat 0)]
      (.error (.limit .natBits))
  let writeArray := { observed with locals := 12 }
  localChecked writeArray links.set #[.erased, fieldArray, field 7, item] (values.set! 7 item)
  localRun { writeArray with locals := 11 } links.set #[.erased, fieldArray, field 7, item] (.error (.limit .locals))
  localRun { writeArray with continuations := 3 } links.set #[.erased, fieldArray, field 7, item] (.error (.limit .continuations))
  localChecked writeArray links.uset #[.erased, fieldArray, raw 7, item, .erased] (values.set! 7 item)
  let pushSpare := { image.state.limits with locals := 13, continuations := 4, natBits := 4, byteArrayBytes := 0 }
  localChecked pushSpare links.push #[.erased, spare, item] ((values.extract 0 7).push item)
  localRun { pushSpare with locals := 12 } links.push #[.erased, spare, item] (.error (.limit .locals))
  localRun { pushSpare with continuations := 3 } links.push #[.erased, spare, item] (.error (.limit .continuations))
  localRun { pushSpare with natBits := 3 } links.push #[.erased, spare, item] (.error (.limit .natBits))
  let pushFull := { pushSpare with locals := 16, continuations := 5, natBits := 5 }
  localChecked pushFull links.push #[.erased, full, item] (values.push item)
  localRun { pushFull with locals := 15 } links.push #[.erased, full, item] (.error (.limit .locals))
  localRun { pushFull with continuations := 4 } links.push #[.erased, full, item] (.error (.limit .continuations))
  localRun { pushFull with natBits := 4 } links.push #[.erased, full, item] (.error (.limit .natBits))
  let smallFull := array 0 (cached 1) leaf
  localChecked { pushFull with continuations := 2, natBits := 2 } links.push #[.erased, smallFull, item]
    #[.scalar (.word32 99), item]
  -- Input validation establishes structural validity, independently of the
  -- live-prefix invariant required by the source contracts.
  let missingLeaf := array 0 (cached 1) empty
  localRun observed links.get #[.erased, missingLeaf, cached 0, .erased] (.error (.invalidProjection 0))
  IO.println s!"check-ixby-lean array resources: {← count.get} exact capacity cases"

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
  natArithmeticMutations runtimeImage
  natArithmeticExecutions runtimeImage
  fieldMutations runtimeImage
  fieldExecutions runtimeImage
  natLoopMutations runtimeImage
  natLoopExecutions runtimeImage
  wordMutations runtimeImage
  wordExecutions runtimeImage
  arrayTreeMutations runtimeImage
  arrayTreeExecutions runtimeImage
  arrayTreeResources runtimeImage
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
