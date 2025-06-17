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
⟧

structure TestCase where
  functionName : Lean.Name
  input : Array UInt64
  expectedOutput : Array UInt64

def testCases : List TestCase := [
    ⟨`id, #[42], #[42]⟩,
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
    ⟨`fibonacci, #[5], #[8]⟩,
  ]

def aiurTest : TestSeq :=
  withExceptOk "Check and simplification works" (checkAndSimplifyToplevel toplevel) fun decls =>
    let bytecodeToplevel := decls.compile
    let (aiurCircuits, funcChannel) := Circuit.synthesize bytecodeToplevel
    let circuitModules := aiurCircuits.circuitModules
    let runTestCase := fun (testCase : TestCase) =>
      let functionName := testCase.functionName
      let funcIdx := toplevel.getFuncIdx functionName |>.get!.toUInt64
      let record := bytecodeToplevel.execute funcIdx testCase.input
      let output := record.getFuncResult funcIdx testCase.input |>.get!
      let executionTest :=
        test s!"Result of {functionName} is correct" (output == testCase.expectedOutput)
      let traces := bytecodeToplevel.generateTraces record
      let witness := Circuit.populateWitness aiurCircuits traces
      let boundaries := Circuit.mkBoundaries testCase.input output funcIdx funcChannel
      let witnessTest :=
        withExceptOk s!"Witness for {functionName} with arguments {testCase.input} is accepted"
          (Archon.validateWitness circuitModules boundaries witness) fun _ => .done
      executionTest ++ witnessTest
    testCases.foldl (init := .done) fun tSeq testCase =>
      tSeq ++ runTestCase testCase

def Tests.Aiur.suite := [aiurTest]
