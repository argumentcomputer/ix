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
