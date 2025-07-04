import LSpec
import Ix.Aiur.Bytecode
import Ix.Aiur.Simple
import Ix.Aiur.Meta
import Ix.Aiur.Execute
import Ix.Aiur.Witness
import Ix.Archon.Protocol

open LSpec Aiur

def toplevel := ⟦
  fn id(n: u64) -> u64 {
    n
  }

  fn proj1(a: u64, _b: u64) -> u64 {
    a
  }

  fn sum(x: u64, y: u64) -> u64 {
    add(x, y)
  }

  fn prod(x: u64, y: u64) -> u64 {
    mul(x, y)
  }

  fn store_and_load(x: u64) -> u64 {
    load(store(x))
  }

  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn even(m: Nat) -> u1 {
    match m {
      Nat.Zero => 1u1,
      Nat.Succ(m) => odd(load(m)),
    }
  }

  fn odd(m: Nat) -> u1 {
    match m {
      Nat.Zero => 0u1,
      Nat.Succ(m) => even(load(m)),
    }
  }

  fn is_0_even() -> u1 {
    even(Nat.Zero)
  }

  fn is_1_even() -> u1 {
    even(Nat.Succ(store(Nat.Zero)))
  }

  fn is_2_even() -> u1 {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }

  fn is_3_even() -> u1 {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))
  }

  fn is_4_even() -> u1 {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))))
  }

  fn is_0_odd() -> u1 {
    odd(Nat.Zero)
  }

  fn is_1_odd() -> u1 {
    odd(Nat.Succ(store(Nat.Zero)))
  }

  fn is_2_odd() -> u1 {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }

  fn is_3_odd() -> u1 {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))
  }

  fn is_4_odd() -> u1 {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))))
  }

  fn factorial(n: u64) -> u64 {
    if n {
      mul(n, factorial(sub(n, 1u64)))
    } else {
      1u64
    }
  }

  fn fibonacci(n: u64) -> u64 {
    if n {
      let n_minus_1 = sub(n, 1u64);
      if n_minus_1 {
        let n_minus_2 = sub(n_minus_1, 1u64);
        add(fibonacci(n_minus_1), fibonacci(n_minus_2))
      } else {
        1u64
      }
    } else {
      1u64
    }
  }

  fn call_bit_xor(a: u64, b: u64) -> u64 {
    let c = ffi(bit_xor, a, b);
    get(c, 0)
  }

  fn call_bit_xor2(a: u64, b: u64) -> u64 {
    let (c) = ffi(bit_xor, a, b);
    c
  }

  fn slice_and_get(as: (u64, u64, u64, u64)) -> u64 {
    get(slice(as, 1, 4), 2)
  }
⟧

open Archon Binius

def bitXor : Gadget :=
  { name := `bit_xor
    inputSize := 2
    outputSize := 1
    execute := fun inp => #[inp[0]! ^^^ inp[1]!]
    synthesize
    populate }
where
  synthesize channelId circuitModule :=
    let circuitModule := circuitModule.pushNamespace "bit-xor"
    let (xBits, circuitModule) := circuitModule.addCommitted "x-bits" .b1 (.mul2 6)
    let (yBits, circuitModule) := circuitModule.addCommitted "y-bits" .b1 (.mul2 6)
    let (multiplicity, circuitModule) := circuitModule.addCommitted "multiplicity" .b64 .base
    let (zBits, circuitModule) := circuitModule.addLinearCombination "z-bits" 0
      #[(xBits, 1), (yBits, 1)] (.mul2 6)
    let (x, circuitModule) := circuitModule.addPacked "x-bits-packed" xBits 6
    let (y, circuitModule) := circuitModule.addPacked "y-bits-packed" yBits 6
    let (z, circuitModule) := circuitModule.addPacked "z-bits-packed" zBits 6
    let args := #[x, y, z].map .oracle
    let circuitModule := Gadget.provide circuitModule channelId multiplicity args
    (circuitModule.popNamespace, #[xBits, yBits, multiplicity])
  populate entries oracles witnessModule :=
    if entries.isEmpty then (witnessModule, .inactive) else
      let height := entries.size.nextPowerOfTwo.max 2
      let logHeight := height.log2.toUInt8
      let mode := .active logHeight entries.size.toUInt64
      let xBits := oracles[0]!
      let yBits := oracles[1]!
      let multiplicity := oracles[2]!
      let (xBitsEntry, witnessModule) := witnessModule.addEntryWithCapacity (logHeight + 6)
      let (yBitsEntry, witnessModule) := witnessModule.addEntryWithCapacity (logHeight + 6)
      let (multiplicityEntry, witnessModule) := witnessModule.addEntryWithCapacity logHeight
      let witnessModule := witnessModule.bindOracleTo xBits xBitsEntry .b1
      let witnessModule := witnessModule.bindOracleTo yBits yBitsEntry .b1
      let witnessModule := witnessModule.bindOracleTo multiplicity multiplicityEntry .b64
      let (xData, yData, mData) := entries.foldl (init := (#[], #[], #[]))
        fun (xData, yData, mData) entry =>
          let multiplicity := powUInt64InBinaryField MultiplicativeGenerator entry.multiplicity
          (xData.push entry.input[0]!, yData.push entry.input[1]!, mData.push multiplicity)
      let witnessModule := witnessModule.pushUInt64sTo xData xBitsEntry
      let witnessModule := witnessModule.pushUInt64sTo yData yBitsEntry
      let witnessModule := witnessModule.pushUInt64sTo mData multiplicityEntry
      (witnessModule, mode)

structure TestCase where
  functionName : Lean.Name
  input : Array UInt64
  expectedOutput : Array UInt64

def testCases : List TestCase := [
    ⟨`id, #[42], #[42]⟩,
    ⟨`proj1, #[42, 64], #[42]⟩,
    ⟨`sum, #[3, 5], #[8]⟩,
    ⟨`prod, #[3, 5], #[15]⟩,
    ⟨`store_and_load, #[42], #[42]⟩,
    ⟨`is_0_even, #[], #[1]⟩,
    ⟨`is_1_even, #[], #[0]⟩,
    ⟨`is_2_even, #[], #[1]⟩,
    ⟨`is_3_even, #[], #[0]⟩,
    ⟨`is_4_even, #[], #[1]⟩,
    ⟨`is_0_odd, #[], #[0]⟩,
    ⟨`is_1_odd, #[], #[1]⟩,
    ⟨`is_2_odd, #[], #[0]⟩,
    ⟨`is_3_odd, #[], #[1]⟩,
    ⟨`is_4_odd, #[], #[0]⟩,
    ⟨`factorial, #[5], #[120]⟩,
    ⟨`fibonacci, #[0], #[1]⟩,
    ⟨`fibonacci, #[1], #[1]⟩,
    ⟨`fibonacci, #[6], #[13]⟩,
    ⟨`call_bit_xor, #[13, 7], #[10]⟩,
    ⟨`call_bit_xor2, #[13, 7], #[10]⟩,
    ⟨`slice_and_get, #[1, 2, 3, 4], #[4]⟩,
  ]

def aiurTest : TestSeq :=
  let toplevel := toplevel.addGadget bitXor
  withExceptOk "Check and simplification works" (checkAndSimplifyToplevel toplevel) fun decls =>
    let bytecodeToplevel := decls.compile
    let (aiurCircuits, funcChannels) := Circuit.synthesize bytecodeToplevel
    let circuitModules := aiurCircuits.circuitModules
    let runTestCase := fun (testCase : TestCase) =>
      let functionName := testCase.functionName
      let funcIdx := toplevel.getFuncIdx functionName |>.get!
      let record := bytecodeToplevel.execute funcIdx testCase.input
      let output := record.getFuncResult funcIdx testCase.input |>.get!
      let executionTest :=
        test s!"Result of {functionName} with arguments {testCase.input} is correct"
          (output == testCase.expectedOutput)
      let traces := bytecodeToplevel.generateTraces record
      let witness := Circuit.populateWitness aiurCircuits traces bytecodeToplevel.gadgets
      let funcChannel := funcChannels[funcIdx]!
      let boundaries := Circuit.mkBoundaries testCase.input output funcChannel
      let witnessTest :=
        withExceptOk s!"Witness for {functionName} with arguments {testCase.input} is accepted"
          (Archon.validateWitness circuitModules boundaries witness) fun _ => .done
      let (logInvRate, securityBits) := (1, 100)
      let proof := Archon.prove circuitModules boundaries logInvRate securityBits witness
      let proofTest :=
        withExceptOk s!"Proof for {functionName} with arguments {testCase.input} verifies"
          (Archon.verify circuitModules boundaries logInvRate securityBits proof) fun _ => .done
      executionTest ++ witnessTest ++ proofTest
    testCases.foldl (init := .done) fun tSeq testCase =>
      tSeq ++ runTestCase testCase

def Tests.Aiur.suite := [aiurTest]
