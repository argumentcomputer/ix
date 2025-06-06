import LSpec
import Ix.Aiur.Bytecode
import Ix.Aiur.Simple
import Ix.Aiur.Meta
import Ix.Aiur.Execute

open LSpec Aiur

def toplevel := ⟦
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
⟧

structure ExecutionTestCase where
  functionName : Lean.Name
  input : Array UInt64
  expectedOutput : Array UInt64

def executionTestCases : List ExecutionTestCase := [
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
  ]

def testExecute : TestSeq :=
  withExceptOk "Check and simplification works" (checkAndSimplifyToplevel toplevel) fun decls =>
    let bytecodeToplevel := decls.compile
    let runExecutionTestCase := fun (testCase : ExecutionTestCase) =>
      let functionName := testCase.functionName
      let funcIdx := toplevel.getFuncIdx functionName |>.get!.toUInt64
      let record := bytecodeToplevel.execute funcIdx testCase.input
      let values := record.getFuncResult funcIdx testCase.input |>.get!
      test s!"Result of {functionName} is correct" (values == testCase.expectedOutput)
    executionTestCases.foldl (init := .done) fun tSeq testCase =>
      tSeq ++ runExecutionTestCase testCase

def Tests.Aiur.suite := [
    testExecute,
  ]
