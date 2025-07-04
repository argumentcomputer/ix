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

  fn call_u32nucleate4(
    a0: u64,
    a1: u64,
    a2: u64,
    a3: u64
  ) -> (u64, u64, u64, u64, u64, u64, u64, u64) {
    ffi(u32nucleate4, a0, a1, a2, a3)
  }

  fn call_rotate_right16(a: u64) -> u64 {
    let (c) = ffi(rotate_right16, a);
    c
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

def u32nucleate4 : Gadget :=
{
  name := `u32nucleate4
  inputSize := 4
  outputSize := 8
  execute
  synthesize
  populate
} where
  execute input :=
    let u32nucleate (input : Array UInt64) : Array UInt32 :=
      input.flatMap (fun item => #[
        UInt32.ofBitVec ((item.shiftRight 32).toBitVec.truncate 32),
        UInt32.ofBitVec (item.toBitVec.truncate 32),
      ])
    let nucleated := u32nucleate #[input[0]!, input[1]!, input[2]!, input[3]!]
    nucleated.map (fun i => i.toUInt64)

  synthesize channelId circuitModule :=
    let circuitModule := circuitModule.pushNamespace "nucleate4"
    let (a0, circuitModule) := circuitModule.addCommitted "a0" .b1 (.mul2 6)
    let (a1, circuitModule) := circuitModule.addCommitted "a1" .b1 (.mul2 6)
    let (a2, circuitModule) := circuitModule.addCommitted "a2" .b1 (.mul2 6)
    let (a3, circuitModule) := circuitModule.addCommitted "a3" .b1 (.mul2 6)

    let (multiplicity, circuitModule) := circuitModule.addCommitted "multiplicity" .b64 .base

    let (out0, circuitModule) := circuitModule.addShifted "out0" a0 32 6 .logicalRight
    let (out1Temp, circuitModule) := circuitModule.addShifted "out1Temp" a0 32 6 .logicalLeft
    let (out1, circuitModule) := circuitModule.addShifted "out1" out1Temp 32 6 .logicalRight

    let (out2, circuitModule) := circuitModule.addShifted "out2" a1 32 6 .logicalRight
    let (out3Temp, circuitModule) := circuitModule.addShifted "out3Temp" a1 32 6 .logicalLeft
    let (out3, circuitModule) := circuitModule.addShifted "out3" out3Temp 32 6 .logicalRight

    let (out4, circuitModule) := circuitModule.addShifted "out4" a2 32 6 .logicalRight
    let (out5Temp, circuitModule) := circuitModule.addShifted "out5Temp" a2 32 6 .logicalLeft
    let (out5, circuitModule) := circuitModule.addShifted "out5" out5Temp 32 6 .logicalRight

    let (out6, circuitModule) := circuitModule.addShifted "out6" a3 32 6 .logicalRight
    let (out7Temp, circuitModule) := circuitModule.addShifted "out7Temp" a3 32 6 .logicalLeft
    let (out7, circuitModule) := circuitModule.addShifted "out7" out7Temp 32 6 .logicalRight

    let (a0p, circuitModule) := circuitModule.addPacked "a0-packed" a0 6
    let (a1p, circuitModule) := circuitModule.addPacked "a1-packed" a1 6
    let (a2p, circuitModule) := circuitModule.addPacked "a2-packed" a2 6
    let (a3p, circuitModule) := circuitModule.addPacked "a3-packed" a3 6

    let (out0p, circuitModule) := circuitModule.addPacked "out0-packed" out0 6
    let (out1p, circuitModule) := circuitModule.addPacked "out1-packed" out1 6
    let (out2p, circuitModule) := circuitModule.addPacked "out2-packed" out2 6
    let (out3p, circuitModule) := circuitModule.addPacked "out3-packed" out3 6
    let (out4p, circuitModule) := circuitModule.addPacked "out4-packed" out4 6
    let (out5p, circuitModule) := circuitModule.addPacked "out5-packed" out5 6
    let (out6p, circuitModule) := circuitModule.addPacked "out6-packed" out6 6
    let (out7p, circuitModule) := circuitModule.addPacked "out7-packed" out7 6

    let args := #[a0p, a1p, a2p, a3p, out0p, out1p, out2p, out3p, out4p, out5p, out6p, out7p]

    let circuitModule := Gadget.provide circuitModule channelId multiplicity (args.map .oracle)

    (circuitModule.popNamespace, (#[a0, a1, a2, a3, multiplicity]))

  populate entries oracles witnessModule :=
    if entries.isEmpty then (witnessModule, .inactive) else
      let height := entries.size.nextPowerOfTwo.max 2
      let log2Height := height.log2.toUInt8

      let a0 := oracles[0]!
      let a1 := oracles[1]!
      let a2 := oracles[2]!
      let a3 := oracles[3]!
      let multiplicity := oracles[4]!

      let (a0Data, a1Data, a2Data, a3Data, multiplicityData) :=
        entries.foldl (init := (#[], #[], #[], #[], #[]))
          fun (a0, a1, a2, a3, multiplicityData) entry =>
            let multiplicity := powUInt64InBinaryField MultiplicativeGenerator entry.multiplicity
            (
              a0.push entry.input[0]!,
              a1.push entry.input[1]!,
              a2.push entry.input[2]!,
              a3.push entry.input[3]!,
              multiplicityData.push multiplicity
            )

      let (a0Entry, witnessModule) := witnessModule.addEntry
      let (a1Entry, witnessModule) := witnessModule.addEntry
      let (a2Entry, witnessModule) := witnessModule.addEntry
      let (a3Entry, witnessModule) := witnessModule.addEntry
      let (multiplicityEntry, witnessModule) := witnessModule.addEntry

      let witnessModule := witnessModule.pushUInt64sTo a0Data a0Entry
      let witnessModule := witnessModule.pushUInt64sTo a1Data a1Entry
      let witnessModule := witnessModule.pushUInt64sTo a2Data a2Entry
      let witnessModule := witnessModule.pushUInt64sTo a3Data a3Entry
      let witnessModule := witnessModule.pushUInt64sTo multiplicityData multiplicityEntry

      let witnessModule := witnessModule.bindOracleTo a0 a0Entry .b1
      let witnessModule := witnessModule.bindOracleTo a1 a1Entry .b1
      let witnessModule := witnessModule.bindOracleTo a2 a2Entry .b1
      let witnessModule := witnessModule.bindOracleTo a3 a3Entry .b1
      let witnessModule := witnessModule.bindOracleTo multiplicity multiplicityEntry .b64

      (witnessModule, .active log2Height entries.size.toUInt64 )

def rotateRight16 : Gadget :=
{
  name := `rotate_right16
  inputSize := 1
  outputSize := 1
  execute := fun input =>
    let x := input[0]!
    #[UInt64.ofBitVec (x.toBitVec.rotateRight 16)]
  synthesize
  populate
}
where
  synthesize channelId circuitModule :=
    let (aIn, circuitModule) := circuitModule.addCommitted "aIn" .b1 (.mul2 6)
    let (multiplicity, circuitModule) := circuitModule.addCommitted "multiplicity" .b64 .base
    let (out, circuitModule) := circuitModule.addShifted "out" aIn (64 - 16) 6 .circularLeft

    let (aInPacked, circuitModule) := circuitModule.addPacked "aInPacked" aIn 6
    let (outPacked, circuitModule) := circuitModule.addPacked "out" out 6
    let args := #[aInPacked, outPacked].map .oracle

    let circuitModule := Gadget.provide circuitModule channelId multiplicity args

    (circuitModule, #[aIn, multiplicity])

  populate entries oracles witnessModule :=
    if entries.isEmpty then (witnessModule, .inactive) else
      let height := entries.size.nextPowerOfTwo.max 2
      let log2Height := height.log2.toUInt8

      let aIn := oracles[0]!
      let multiplicity := oracles[1]!

      let (aData, multiplicityData) := entries.foldl (init := (#[], #[]))
        fun (a, mult) entry =>
          let multiplicity := powUInt64InBinaryField MultiplicativeGenerator entry.multiplicity
          (a.push entry.input[0]!, mult.push multiplicity)

      let (aEntry, witnessModule) := witnessModule.addEntry
      let (multiplicityEntry, witnessModule) := witnessModule.addEntry

      let witnessModule := witnessModule.pushUInt64sTo aData aEntry
      let witnessModule := witnessModule.pushUInt64sTo multiplicityData multiplicityEntry

      let witnessModule := witnessModule.bindOracleTo aIn aEntry .b1
      let witnessModule := witnessModule.bindOracleTo multiplicity multiplicityEntry .b64

      (witnessModule, .active log2Height entries.size.toUInt64)

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
    ⟨`call_u32nucleate4, #[
      0x1111111122222222,
      0x3333333344444444,
      0x5555555566666666,
      0xaaaaaaaabbbbbbbb,
    ], #[
      0x11111111,
      0x22222222,
      0x33333333,
      0x44444444,
      0x55555555,
      0x66666666,
      0xaaaaaaaa,
      0xbbbbbbbb,
    ]⟩,
    ⟨`call_rotate_right16, #[0xaaaaaaaaffffffff], #[0xffffaaaaaaaaffff] ⟩
  ]

def aiurTest : TestSeq :=
  let toplevel := toplevel.addGadget bitXor
  let toplevel := toplevel.addGadget u32nucleate4
  let toplevel := toplevel.addGadget rotateRight16

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
