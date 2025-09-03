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
    x + y
  }

  fn prod(x: G, y: G) -> G {
    x * y
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
      _ => n * factorial(n - 1),
    }
  }

  fn fibonacci(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let n_minus_1 = n - 1;
        match n_minus_1 {
          0 => 1,
          _ =>
            let n_minus_2 = n_minus_1 - 1;
            fibonacci(n_minus_1) + fibonacci(n_minus_2),
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

  fn deconstruct_tuple(as: (G, G, G, G, G)) -> (G, G) {
    let (_, b, _, d, _) = as;
    (b, d)
  }

  fn deconstruct_array(as: [G; 5]) -> [G; 2] {
    let [_, b, _, d, _] = as;
    [b, d]
  }

  fn read_write_io() -> G {
    let (idx, len) = io_get_info([0]);
    let xs: [G; 4] = io_read(idx, 4);
    io_write(xs);
    io_set_info([1], idx, len + 4);
    len
  }

  fn shr_shr_shl_decompose(byte: G) -> [G; 8] {
    let byte_shr = u8_shift_right(byte);
    let byte_shr_shr = u8_shift_right(byte_shr);
    let byte_shr_shr_shl = u8_shift_left(byte_shr_shr);
    u8_bit_decomposition(byte_shr_shr_shl)
  }

  fn u8_add_xor(i: G, j: G) -> ((G, G), (G, G)) {
    let i_xor_j = u8_xor(i, j);
    (u8_add(i_xor_j, i), u8_add(i_xor_j, j))
  }
⟧

structure TestCase where
  functionName : Lean.Name
  input : Array Aiur.G
  expectedOutput : Array Aiur.G
  inputIOBuffer: Aiur.IOBuffer
  expectedIOBuffer: Aiur.IOBuffer

def testCases : List TestCase := [
    ⟨`id, #[42], #[42], default, default⟩,
    ⟨`proj1, #[42, 64], #[42], default, default⟩,
    ⟨`sum, #[3, 5], #[8], default, default⟩,
    ⟨`prod, #[3, 5], #[15], default, default⟩,
    ⟨`store_and_load, #[42], #[42], default, default⟩,
    ⟨`is_0_even, #[], #[1], default, default⟩,
    ⟨`is_1_even, #[], #[0], default, default⟩,
    ⟨`is_2_even, #[], #[1], default, default⟩,
    ⟨`is_3_even, #[], #[0], default, default⟩,
    ⟨`is_4_even, #[], #[1], default, default⟩,
    ⟨`is_0_odd, #[], #[0], default, default⟩,
    ⟨`is_1_odd, #[], #[1], default, default⟩,
    ⟨`is_2_odd, #[], #[0], default, default⟩,
    ⟨`is_3_odd, #[], #[1], default, default⟩,
    ⟨`is_4_odd, #[], #[0], default, default⟩,
    ⟨`factorial, #[5], #[120], default, default⟩,
    ⟨`fibonacci, #[0], #[1], default, default⟩,
    ⟨`fibonacci, #[1], #[1], default, default⟩,
    ⟨`fibonacci, #[6], #[13], default, default⟩,
    ⟨`projections, #[1, 2, 3, 4, 5], #[2, 4], default, default⟩,
    ⟨`slice_and_get, #[1, 2, 3, 4, 5], #[2, 4], default, default⟩,
    ⟨`deconstruct_tuple, #[1, 2, 3, 4, 5], #[2, 4], default, default⟩,
    ⟨`deconstruct_array, #[1, 2, 3, 4, 5], #[2, 4], default, default⟩,
    ⟨`read_write_io, #[], #[4],
      ⟨#[1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩)]⟩,
      ⟨#[1, 2, 3, 4, 1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩), (#[1], ⟨0, 8⟩)]⟩⟩,
    ⟨`shr_shr_shl_decompose, #[87], #[0, 1, 0, 1, 0, 1, 0, 0], default, default⟩,
    ⟨`u8_add_xor, #[45, 131], #[219, 0, 49, 1], default, default⟩,
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
      let (claim, proof, ioBuffer) := aiurSystem.prove
        friParameters funIdx testCase.input testCase.inputIOBuffer
      let caseDescr := s!"{functionName} with arguments {testCase.input}"
      let claimTest := test s!"Claim matches for {caseDescr}"
        (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
      let ioTest := test s!"IOBuffer matches for {caseDescr}"
        (ioBuffer == testCase.expectedIOBuffer)
      let proof := .ofBytes proof.toBytes
      let pvTest := withExceptOk s!"Prove/verify works for {caseDescr}"
        (aiurSystem.verify friParameters claim proof) fun _ => .done
      claimTest ++ ioTest ++ pvTest
    testCases.foldl (init := .done) fun tSeq testCase =>
      tSeq ++ runTestCase testCase

def Tests.Aiur.suite := [aiurTest]
