module

public import Tests.Aiur.Common
public import Ix.Aiur.Meta

public section

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

  fn sum_prod(x: G, y: G, z: G) -> G {
    (x + y) * z
  }

  ---------------------------------------------------------------------------
  -- Match coverage: active/inactive paths, inequality witnesses, nesting
  ---------------------------------------------------------------------------

  -- 1 explicit case + default. Default branch has degree-2+ Mul.
  -- x=0: explicit active, default's Mul constraints inactive.
  -- x≠0: default active, explicit inactive.
  fn match_mul(x: G) -> G {
    match x {
      0 => 0,
      _ => x * x * x,
    }
  }

  -- 3 explicit cases + default. Default path requires 3 inequality witnesses.
  fn multi_match(x: G) -> G {
    match x {
      0 => 100,
      1 => 200,
      2 => 300,
      _ => x * x,
    }
  }

  -- Nested match: outer block selector = sum of inner selectors. Tests
  -- inequality witnesses at both nesting levels and computation in the
  -- deepest default path.
  fn nested_match(x: G, y: G) -> G {
    match x {
      0 => match y {
        0 => 10,
        _ => 20,
      },
      _ => match y {
        0 => 30,
        _ => x + y,
      },
    }
  }

  ---------------------------------------------------------------------------
  -- Active/inactive sel-gating: polynomial constraints
  --
  -- The inactive branch (case 1) has DIFFERENT computations from the active
  -- branch (case 0), so the shared auxiliary columns hold "wrong" values for
  -- the inactive branch. Additionally, assert_eq!(0, 1) on the inactive path
  -- produces constraint sel * (0 - 1) = -sel, which is 0 only when sel = 0.
  ---------------------------------------------------------------------------
  fn match_poly_ops(x: G) -> (G, G) {
    match 0 {
      0 => assert_eq!([x], [x]); (x * x, eq_zero(x)),
      1 => assert_eq!([0], [1]); ((x + 1) * (x + 1), eq_zero(x + 1)),
    }
  }

  ---------------------------------------------------------------------------
  -- Active/inactive sel-gating: lookup multiplicities
  --
  -- Same operations in both branches. If lookup multiplicity were not gated
  -- by sel, both branches would contribute multiplicity, doubling it from 1
  -- to 2 and failing the lookup argument check.
  ---------------------------------------------------------------------------
  fn match_lookup_ops(x: G) -> (G, G) {
    match 0 {
      0 => (id(x), load(store(x))),
      1 => (id(x), load(store(x))),
    }
  }

  ---------------------------------------------------------------------------
  -- Active/inactive sel-gating: gadget lookups + U32LessThan constraints
  --
  -- Same Bytes1/Bytes2 ops test lookup multiplicity gating. Swapped args for
  -- U32LessThan on the inactive path create mismatched byte decompositions
  -- and carry chains in the shared auxiliary columns, testing that the
  -- polynomial constraints (decomposition + carry boolean) are properly gated.
  ---------------------------------------------------------------------------
  fn match_gadget_ops(i: G, j: G) -> (G, G, G) {
    match 0 {
      0 => (u8_shift_right(i), u8_xor(i, j), u32_less_than(i, j)),
      1 => (u8_shift_right(i), u8_xor(i, j), u32_less_than(j, i)),
    }
  }

  ---------------------------------------------------------------------------
  -- Active/inactive sel-gating: multi-output gadget lookups
  --
  -- u8_add has output_size=2, testing the same missing-sel bug in
  -- bytes2_constraints for the multi-output case. u8_bit_decomposition has
  -- output_size=8, testing it for bytes1_constraints.
  ---------------------------------------------------------------------------
  fn match_gadget_ops_multi(i: G, j: G) -> ((G, G), [G; 8]) {
    match 0 {
      0 => (u8_add(i, j), u8_bit_decomposition(i)),
      1 => (u8_add(i, j), u8_bit_decomposition(i)),
    }
  }

  ---------------------------------------------------------------------------
  -- EqZero: both constant (degree 0, no constraints) and non-constant
  -- (degree 1, two constraints: sel * a * x = 0, sel * (a*d + x - 1) = 0)
  ---------------------------------------------------------------------------
  fn eq_zero_dummy(a: G, b: G) -> [G; 4] {
    let c = 0;
    let d = 101;
    [eq_zero(a), eq_zero(b), eq_zero(c), eq_zero(d)]
  }

  ---------------------------------------------------------------------------
  -- Memory: store/load
  ---------------------------------------------------------------------------
  fn store_and_load(x: G) -> G {
    load(store(x))
  }

  ---------------------------------------------------------------------------
  -- Enum with 2 constructors, pointer patterns, mutual recursion
  ---------------------------------------------------------------------------
  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn pointer_match() -> G {
    let two = Nat.Succ(store(Nat.Succ(store(Nat.Zero))));
    match two {
      Nat.Succ(&Nat.Succ(&Nat.Zero)) => 1,
      _ => 0,
    }
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

  fn is_0_odd() -> G {
    odd(Nat.Zero)
  }

  fn is_1_odd() -> G {
    odd(Nat.Succ(store(Nat.Zero)))
  }

  ---------------------------------------------------------------------------
  -- 3-constructor enum: tests tag dispatch with 3 cases, constructor field
  -- extraction at different offsets, and padding. Also an implicit
  -- active/inactive Mul test: Circle and Rect both have degree-2 Mul but
  -- with different operands, sharing the same auxiliary column.
  --
  -- Datatype size = max(|Circle|, |Rect|, |Tri|) + 1 = 3 + 1 = 4
  -- Circle(r):    [0, r, pad, pad]
  -- Rect(w, h):   [1, w, h, pad]
  -- Tri(a, b, c): [2, a, b, c]
  ---------------------------------------------------------------------------
  enum Shape {
    Circle(G),
    Rect(G, G),
    Tri(G, G, G)
  }

  fn shape_area(s: Shape) -> G {
    match s {
      Shape.Circle(r) => r * r,
      Shape.Rect(w, h) => w * h,
      Shape.Tri(a, b, c) => a + b + c,
    }
  }

  ---------------------------------------------------------------------------
  -- Constrained and unconstrained recursion (fibonacci tests left intact)
  ---------------------------------------------------------------------------
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

  #[unconstrained]
  fn unconstrained_fibonacci(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let n_minus_1 = n - 1;
        match n_minus_1 {
          0 => 1,
          _ =>
            let n_minus_2 = n_minus_1 - 1;
            fibonacci(n_minus_1) + unconstrained_fibonacci(n_minus_2),
        },
    }
  }

  fn unconstrained_fibonacci_entrypoint(n: G) -> G {
    unconstrained_fibonacci(n)
  }

  ---------------------------------------------------------------------------
  -- Data structure compilation: proj, get, slice, set, destructuring
  ---------------------------------------------------------------------------
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

  -- proj on mixed-size tuple: offset arithmetic with non-uniform element sizes
  fn proj_mixed(t: (G, (G, G), G)) -> (G, G) {
    proj(t, 1)
  }

  -- get at last index + set at first index with eltSize=2: boundary cases
  fn array_get_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    let p = arr[2];
    set(arr, 0, p)
  }

  ---------------------------------------------------------------------------
  -- Assertion
  ---------------------------------------------------------------------------
  fn assert_eq_trivial() {
    assert_eq!([1, 2, 3], [1, 2, 3]);
  }

  ---------------------------------------------------------------------------
  -- IO
  ---------------------------------------------------------------------------
  fn read_write_io() {
    let (idx, len) = io_get_info([0]);
    let xs: [G; 4] = io_read(idx, 4);
    io_write(xs);
    io_set_info([1], idx, len + 4);
  }

  ---------------------------------------------------------------------------
  -- Byte operations
  ---------------------------------------------------------------------------
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

  fn u8_sub_function(i: G, j: G) -> (G, G) {
    u8_sub(i, j)
  }

  fn u8_less_than_function(i: G, j: G) -> G {
    u8_less_than(i, j)
  }

  fn u8_and_function(i: G, j: G) -> G {
    u8_and(i, j)
  }

  fn u8_or_function(i: G, j: G) -> G {
    u8_or(i, j)
  }

  ---------------------------------------------------------------------------
  -- u32 comparison
  ---------------------------------------------------------------------------
  fn u32_less_than_function(x: G, y: G) -> G {
    u32_less_than(x, y)
  }

  ---------------------------------------------------------------------------
  -- Fold/iteration
  ---------------------------------------------------------------------------
  fn fold_matrix_sum(m: [[G; 2]; 2]) -> G {
    fold(0 .. 2, 0, |acc_outer, @i|
      fold(0 .. 2, acc_outer, |acc_inner, @j|
        acc_inner + m[@i][@j]
      )
    )
  }
⟧

def aiurTestCases : List AiurTestCase := [
    -- Basic arithmetic
    .noIO `id #[42] #[42],
    .noIO `proj1 #[42, 64] #[42],
    .noIO `sum #[3, 5] #[8],
    .noIO `prod #[3, 5] #[15],
    .noIO `sum_prod #[2, 3, 4] #[20],

    -- Match: 1 explicit case + default, exercise both paths
    { AiurTestCase.noIO `match_mul #[0] #[0] with label := "match_mul(0)" },
    { AiurTestCase.noIO `match_mul #[2] #[8] with label := "match_mul(2)" },

    -- Match: 3 explicit cases + default (3 inequality witnesses on default)
    { AiurTestCase.noIO `multi_match #[0] #[100] with label := "multi_match(0)" },
    { AiurTestCase.noIO `multi_match #[1] #[200] with label := "multi_match(1)" },
    { AiurTestCase.noIO `multi_match #[2] #[300] with label := "multi_match(2)" },
    { AiurTestCase.noIO `multi_match #[5] #[25] with label := "multi_match(5)" },

    -- Nested match: 4 leaf selectors, witnesses at both nesting levels
    { AiurTestCase.noIO `nested_match #[0, 0] #[10]
        with label := "nested_match(0,0)" },
    { AiurTestCase.noIO `nested_match #[0, 1] #[20]
        with label := "nested_match(0,1)" },
    { AiurTestCase.noIO `nested_match #[2, 0] #[30]
        with label := "nested_match(2,0)" },
    { AiurTestCase.noIO `nested_match #[2, 3] #[5]
        with label := "nested_match(2,3)" },

    -- Sel-gating: polynomial constraints (Mul, EqZero, AssertEq).
    -- Inactive branch has assert_eq!(0,1) (fails without sel=0),
    -- different Mul (aux mismatch), different EqZero (witness mismatch).
    -- x=0 chosen so inactive EqZero constraint `sel*(x+1)*x_result =
    -- sel*1*1 = sel` is nonzero without gating.
    .noIO `match_poly_ops #[0] #[0, 1],

    -- Sel-gating: function and memory lookup multiplicity
    .noIO `match_lookup_ops #[42] #[42, 42],

    -- Sel-gating: gadget lookups (Bytes1, Bytes2) and U32LessThan polynomial
    -- constraints (swapped args on inactive path create decomposition mismatch)
    .noIO `match_gadget_ops #[45, 131] #[22, 174, 1],

    -- Sel-gating: multi-output gadget lookups (Bytes2 output_size=2,
    -- Bytes1 output_size=8). Guards against partial fixes that only
    -- address output_size=1.
    .noIO `match_gadget_ops_multi #[45, 131] #[176, 0, 1, 0, 1, 1, 0, 1, 0, 0],

    -- EqZero: constant path (c=0, d=101) and non-constant path (a=0, b=37)
    .noIO `eq_zero_dummy #[0, 37] #[1, 0, 1, 0],

    -- Memory
    .noIO `store_and_load #[42] #[42],
    .noIO `pointer_match #[] #[1],

    -- Mutual recursion: depths 0–2 cover both branches of even/odd
    .noIO `is_0_even #[] #[1],
    .noIO `is_1_even #[] #[0],
    .noIO `is_2_even #[] #[1],
    .noIO `is_0_odd #[] #[0],
    .noIO `is_1_odd #[] #[1],

    -- 3-constructor enum: tag dispatch, field extraction at varying offsets,
    -- padding. Circle and Rect have degree-2 Mul in different branches with
    -- different operands sharing aux columns (implicit sel-gating test).
    -- Circle(5): [tag=0, r=5, pad, pad] → 5*5 = 25
    { AiurTestCase.noIO `shape_area #[0, 5, 0, 0] #[25]
        with label := "shape_area(Circle(5))" },
    -- Rect(3,4): [tag=1, w=3, h=4, pad] → 3*4 = 12
    { AiurTestCase.noIO `shape_area #[1, 3, 4, 0] #[12]
        with label := "shape_area(Rect(3,4))" },
    -- Tri(1,2,3): [tag=2, a=1, b=2, c=3] → 1+2+3 = 6
    { AiurTestCase.noIO `shape_area #[2, 1, 2, 3] #[6]
        with label := "shape_area(Tri(1,2,3))" },

    -- Constrained recursion
    { AiurTestCase.noIO `factorial #[5] #[120] with label := "factorial(5)" },

    -- Fibonacci (left intact)
    { AiurTestCase.noIO `fibonacci #[0] #[1] with label := "fibonacci(0)" },
    { AiurTestCase.noIO `fibonacci #[1] #[1] with label := "fibonacci(1)" },
    { AiurTestCase.noIO `fibonacci #[6] #[13] with label := "fibonacci(6)" },

    -- Unconstrained recursion: mixed constrained/unconstrained calls
    .noIO `unconstrained_fibonacci_entrypoint #[6] #[13],

    -- Data structure compilation
    .noIO `projections #[1, 2, 3, 4, 5] #[2, 4],
    .noIO `slice_and_get #[1, 2, 3, 4, 5] #[2, 4],
    .noIO `deconstruct_tuple #[1, 2, 3, 4, 5] #[2, 4],
    .noIO `deconstruct_array #[1, 2, 3, 4, 5] #[2, 4],
    .noIO `array_set #[1, 1, 2, 2, 3, 3] #[1, 1, 0, 0, 3, 3],
    -- proj on (G, (G,G), G): tests offset arithmetic with mixed element sizes
    .noIO `proj_mixed #[1, 2, 3, 4] #[2, 3],
    -- get at last index + set at first index with eltSize=2: boundary cases
    .noIO `array_get_set #[1, 1, 2, 2, 3, 3] #[3, 3, 2, 2, 3, 3],

    -- Assertion
    .noIO `assert_eq_trivial #[] #[],

    -- IO
    ⟨`read_write_io, "read_write_io", #[], #[],
      ⟨#[1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩)]⟩,
      ⟨#[1, 2, 3, 4, 1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩), (#[1], ⟨0, 8⟩)]⟩⟩,

    -- Byte operations
    .noIO `shr_shr_shl_decompose #[87] #[0, 1, 0, 1, 0, 1, 0, 0],
    .noIO `u8_add_xor #[45, 131] #[219, 0, 49, 1],
    .noIO `u8_sub_function #[45, 131] #[170, 1],
    .noIO `u8_less_than_function #[45, 131] #[1],
    .noIO `u8_and_function #[45, 131] #[1],
    .noIO `u8_or_function #[45, 131] #[175],

    -- u32 comparison: a < b, a > b, a = b
    { AiurTestCase.noIO `u32_less_than_function #[300, 500] #[1]
        with label := "u32_less_than(300,500)" },
    { AiurTestCase.noIO `u32_less_than_function #[500, 300] #[0]
        with label := "u32_less_than(500,300)" },
    { AiurTestCase.noIO `u32_less_than_function #[500, 500] #[0]
        with label := "u32_less_than(500,500)" },

    -- Fold/iteration
    .noIO `fold_matrix_sum #[1, 2, 3, 4] #[10],
  ]

end
