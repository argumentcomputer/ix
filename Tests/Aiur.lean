import Tests.Common
import Ix.Aiur.Meta

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

  fn array_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    set(arr, 1, (0, 0))
  }

  fn assert_eq_trivial() {
    assert_eq!([1, 2, 3], [1, 2, 3]);
  }

  fn read_write_io() {
    let (idx, len) = io_get_info([0]);
    let xs: [G; 4] = io_read(idx, 4);
    io_write(xs);
    io_set_info([1], idx, len + 4);
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

def aiurTestCases : List AiurTestCase := [
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
    ⟨`array_set, #[1, 1, 2, 2, 3, 3], #[1, 1, 0, 0, 3, 3], default, default⟩,
    ⟨`assert_eq_trivial, #[], #[], default, default⟩,
    ⟨`read_write_io, #[], #[],
      ⟨#[1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩)]⟩,
      ⟨#[1, 2, 3, 4, 1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩), (#[1], ⟨0, 8⟩)]⟩⟩,
    ⟨`shr_shr_shl_decompose, #[87], #[0, 1, 0, 1, 0, 1, 0, 0], default, default⟩,
    ⟨`u8_add_xor, #[45, 131], #[219, 0, 49, 1], default, default⟩,
  ]

def Tests.Aiur.suite := [
  mkAiurTests toplevel aiurTestCases
]
