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

  fn call_blake3_compress(
    a0: u64, -- cv
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64, -- block words
    a5: u64,
    a6: u64,
    a7: u64,
    a8: u64,
    a9: u64,
    a10: u64,
    a11: u64,
    a12: u64, -- counter
    a13: u64, -- block_len ([0..32] bits) and flags ([32..64] bits)
    a14: u64, -- output
    a15: u64,
    a16: u64,
    a17: u64,
    a18: u64,
    a19: u64,
    a20: u64,
    a21: u64
  ) -> u64 {
    let (c) = ffi(blake3_compress, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21);
    c
  }

  fn slice_and_get(as: (u64, u64, u64, u64)) -> u64 {
    get(slice(as, 1, 4), 2)
  }
⟧

open Archon Binius

def blake3Compress : Gadget :=
{
  name := `blake3_compress
  inputSize := 22
  outputSize := 1
  execute
  synthesize
  populate
} where
  execute input :=
    let IV : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

    let MSG_PERMUTATION : Vector (Fin 16) 16  := #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
    let A : Vector (Fin 32) 8 := #v[0, 1, 2, 3, 0, 1, 2, 3]
    let B : Vector (Fin 32) 8 := #v[4, 5, 6, 7, 5, 6, 7, 4]
    let C : Vector (Fin 32) 8 := #v[8, 9, 10, 11, 10, 11, 8, 9]
    let D : Vector (Fin 32) 8 := #v[12, 13, 14, 15, 15, 12, 13, 14]
    let MX : Vector (Fin 32) 8 := #v[16, 18, 20, 22, 24, 26, 28, 30]
    let MY : Vector (Fin 32) 8 := #v[17, 19, 21, 23, 25, 27, 29, 31]

    let transition (state: Array UInt32) (j : Fin 8) : Array UInt32 :=
      let aIn := state[(A[j])]!
      let bIn := state[(B[j])]!
      let cIn := state[(C[j])]!
      let dIn := state[(D[j])]!
      let mxIn := state[(MX[j])]!
      let myIn := state[(MY[j])]!

      let a0 := aIn.add (bIn.add mxIn)
      let d0 := UInt32.ofBitVec ((dIn.xor a0).toBitVec.rotateRight 16)
      let c0 := cIn.add d0
      let b0 := UInt32.ofBitVec ((bIn.xor c0).toBitVec.rotateRight 12)

      let a1 := a0.add (b0.add myIn)
      let d1 := UInt32.ofBitVec ((d0.xor a1).toBitVec.rotateRight 8)
      let c1 := c0.add d1
      let b1 := UInt32.ofBitVec ((b0.xor c1).toBitVec.rotateRight 7)

      let state := state.modify (A[j]).toNat fun _ => a1
      let state := state.modify (B[j]).toNat fun _ => b1
      let state := state.modify (C[j]).toNat fun _ => c1
      let state := state.modify (D[j]).toNat fun _ => d1

      state

    let permute (state: Array UInt32) : Array UInt32 :=
      let left := state.extract 0 16
      let right := state.extract 16 32
      let permuted := right.mapIdx (fun i _ =>
        let idx := 16 + MSG_PERMUTATION[i]!.toNat
        state[idx]!
      )
      left ++ permuted

    let roundNoPermute(state: Array UInt32) : Array UInt32 :=
      let state := transition state 0
      let state := transition state 1
      let state := transition state 2
      let state := transition state 3
      let state := transition state 4
      let state := transition state 5
      let state := transition state 6
      let state := transition state 7
      state

    let round (state: Array UInt32) : Array UInt32 :=
      let state := roundNoPermute state
      permute state


    let nucleate (input : Array UInt64) : Array UInt32 :=
      input.flatMap (fun item => #[UInt32.ofBitVec ((item.shiftRight 32).toBitVec.truncate 32), UInt32.ofBitVec (item.toBitVec.truncate 32)])

    let cv := nucleate #[input[0]!, input[1]!, input[2]!, input[3]!]
    let blockWords := nucleate #[input[4]!, input[5]!, input[6]!, input[7]!, input[8]!, input[9]!, input[10]!, input[11]!]
    let counterLow := UInt32.ofBitVec (input[12]!.toBitVec.truncate 32)
    let counterHigh := UInt32.ofBitVec ((input[12]!.shiftRight 32).toBitVec.truncate 32)
    let flags := UInt32.ofBitVec (input[13]!.toBitVec.truncate 32)
    let blockLen := UInt32.ofBitVec ((input[13]!.shiftRight 32).toBitVec.truncate 32)
    let output := nucleate #[input[14]!, input[15]!, input[16]!, input[17]!, input[18]!, input[19]!, input[20]!, input[21]!]

    let state := cv ++ (IV.extract 0 4) ++ #[counterLow, counterHigh, blockLen, flags] ++ blockWords

    let state := round state
    let state := round state
    let state := round state
    let state := round state
    let state := round state
    let state := round state
    let state := roundNoPermute state

    let temp := ((state.extract 0 8).zipWith (Xor.xor) (state.extract 8 16))
    let state := temp.append (state.extract 8 32)
    let temp := (state.extract 8 16).zipWith (Xor.xor) cv
    let state := state.extract 0 8 ++ temp ++ state.extract 16 32

    if output != state.extract 0 16 then #[0] else #[1]

  synthesize channelId circuitModule :=
    -- TODO: figure out how to combine columns/constraints that I have in isolated, out-of-aiur Blake3 gadget (Archon modules) with aiur-speicific columns related to provide/require protocol
    (circuitModule, #[])

  populate entries oracles witnessModule :=
    -- TODO: figure out how trace generation works in Aiur and how can I: 1) satisfy provide / require protocol; 2) populate witness
    dbg_trace entries.size

    let (xData, yData, mData) := entries.foldl (init := (#[], #[], #[]))
      fun (xData, yData, mData) entry =>

        dbg_trace s!"input: {entry.input}"
        dbg_trace s!"output: {entry.output}"
        dbg_trace s!"multiplicity: {entry.multiplicity}"

        let multiplicity := powUInt64InBinaryField MultiplicativeGenerator entry.multiplicity
        (xData.push entry.input[0]!, yData.push entry.input[1]!, mData.push multiplicity)


    (witnessModule, .inactive)

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
    let circuitModule := circuitModule.flush .push channelId CircuitModule.selector
      (args.push (.const 1 .b1)) 1
    let circuitModule := circuitModule.flush .pull channelId CircuitModule.selector
      (args.push (.oracle multiplicity)) 1
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

          dbg_trace entry.input
          dbg_trace entry.output
          dbg_trace entry.multiplicity

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
    -- ⟨`id, #[42], #[42]⟩,
    -- ⟨`proj1, #[42, 64], #[42]⟩,
    -- ⟨`sum, #[3, 5], #[8]⟩,
    -- ⟨`prod, #[3, 5], #[15]⟩,
    -- ⟨`store_and_load, #[42], #[42]⟩,
    -- ⟨`is_0_even, #[], #[1]⟩,
    -- ⟨`is_1_even, #[], #[0]⟩,
    -- ⟨`is_2_even, #[], #[1]⟩,
    -- ⟨`is_3_even, #[], #[0]⟩,
    -- ⟨`is_4_even, #[], #[1]⟩,
    -- ⟨`is_0_odd, #[], #[0]⟩,
    -- ⟨`is_1_odd, #[], #[1]⟩,
    -- ⟨`is_2_odd, #[], #[0]⟩,
    -- ⟨`is_3_odd, #[], #[1]⟩,
    -- ⟨`is_4_odd, #[], #[0]⟩,
    -- ⟨`factorial, #[5], #[120]⟩,
    -- ⟨`fibonacci, #[0], #[1]⟩,
    -- ⟨`fibonacci, #[1], #[1]⟩,
    -- ⟨`fibonacci, #[6], #[13]⟩,
    -- ⟨`call_bit_xor, #[13, 7], #[10]⟩,
    -- ⟨`call_bit_xor2, #[13, 7], #[10]⟩,
    -- ⟨`slice_and_get, #[1, 2, 3, 4], #[4]⟩,

    ⟨ `call_blake3_compress, #[
        0xffffffffffffffff, -- cv
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xaa000000aa000000, -- blockWords
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xaa000000aa000000,
        0xbbbbbbbbcccccccc, -- counter
        0xeeeeeeeedddddddd, -- block_len | flags
        0x8980fe1555898ce0, -- output
        0x8cf4fbde5e8537e9,
        0x03d2e54f7e46753f,
        0x5d151bb82559b733,
        0x245609296625b1bf,
        0xaaccc80ec5d4287a,
        0x2848c46b094f666c,
        0x3adaaeb312011250
      ], #[1] ⟩,
  ]

def aiurTest : TestSeq :=
  let toplevel := toplevel.addGadget bitXor
  let toplevel := toplevel.addGadget blake3Compress

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
