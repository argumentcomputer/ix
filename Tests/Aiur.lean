import LSpec
import Ix.Aiur.Meta
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol

open LSpec

def toplevel := ⟦
  fn id(n: G) -> G {
    n
  }

  fn proj1(a: G, _b: G) -> G {
    a
  }

  fn sum(x: G, y: G) -> G {
    add(x, y)
  }

  fn prod(x: G, y: G) -> G {
    mul(x, y)
  }

  fn store_and_load(x: G) -> G {
    load(store(x))
  }

  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn even(m: Nat) -> G {
    match m {
      Nat.Zero => 1,
      Nat.Succ(m) => odd(load(m)),
    }
  }

  fn odd(m: Nat) -> G {
    match m {
      Nat.Zero => 0,
      Nat.Succ(m) => even(load(m)),
    }
  }

  fn is_0_even() -> G {
    even(Nat.Zero)
  }

  fn is_1_even() -> G {
    even(Nat.Succ(store(Nat.Zero)))
  }

  fn is_2_even() -> G {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }

  fn is_3_even() -> G {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))
  }

  fn is_4_even() -> G {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))))
  }

  fn is_0_odd() -> G {
    odd(Nat.Zero)
  }

  fn is_1_odd() -> G {
    odd(Nat.Succ(store(Nat.Zero)))
  }

  fn is_2_odd() -> G {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }

  fn is_3_odd() -> G {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))
  }

  fn is_4_odd() -> G {
    odd(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))))))
  }

  fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => mul(n, factorial(sub(n, 1))),
    }
  }

  fn fibonacci(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let n_minus_1 = sub(n, 1);
        match n_minus_1 {
          0 => 1,
          _ =>
            let n_minus_2 = sub(n_minus_1, 1);
            add(fibonacci(n_minus_1), fibonacci(n_minus_2)),
        },
    }
  }

  fn projections(as: (G, G, G, G, G)) -> (G, G) {
    (proj(as, 1), proj(as, 3))
  }

  fn slice_and_get(as: [G; 5]) -> [G; 2] {
    let left = as[0 .. 2];
    let right = as[3 .. 5];
    [left[1], right[0]]
  }
⟧

structure TestCase where
  functionName : Lean.Name
  input : Array Aiur.G
  expectedOutput : Array Aiur.G

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
    ⟨`projections, #[1, 2, 3, 4, 5], #[2, 4]⟩,
    ⟨`slice_and_get, #[1, 2, 3, 4, 5], #[2, 4]⟩,
  ]

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  proofOfWorkBits := 20
}

def aiurTest : TestSeq :=
  withExceptOk "Check and simplification works" toplevel.checkAndSimplify fun decls =>
    let bytecodeToplevel := decls.compile
    let aiurSystem := Aiur.AiurSystem.build bytecodeToplevel commitmentParameters
    let runTestCase := fun testCase =>
      let functionName := testCase.functionName
      let funIdx := toplevel.getFuncIdx functionName |>.get!
      let (claim, proof) := aiurSystem.prove friParameters funIdx testCase.input
      let caseDescr := s!"{functionName} with arguments {testCase.input}"
      let ioTest := test s!"Claim matches for {caseDescr}"
        (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
      let proof := .ofBytes proof.toBytes
      let pvTest := withExceptOk s!"Prove/verify works for {caseDescr}"
        (aiurSystem.verify friParameters claim proof) fun _ => .done
      ioTest ++ pvTest
    testCases.foldl (init := .done) fun tSeq testCase =>
      tSeq ++ runTestCase testCase

def Tests.Aiur.suite := [aiurTest]
