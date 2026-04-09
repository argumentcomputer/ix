module

public import Tests.Aiur.Common
public import Ix.Aiur.Meta

public section

open LSpec

def toplevel := ⟦
  pub fn id(n: G) -> G {
    n
  }

  pub fn proj1(a: G, _b: G) -> G {
    a
  }

  pub fn sum(x: G, y: G) -> G {
    x + y
  }

  pub fn prod(x: G, y: G) -> G {
    x * y
  }

  pub fn sum_prod(x: G, y: G, z: G) -> G {
    (x + y) * z
  }

  ---------------------------------------------------------------------------
  -- Match coverage: active/inactive paths, inequality witnesses, nesting
  ---------------------------------------------------------------------------

  -- 1 explicit case + default. Default branch has degree-2+ Mul.
  -- x=0: explicit active, default's Mul constraints inactive.
  -- x≠0: default active, explicit inactive.
  pub fn match_mul(x: G) -> G {
    match x {
      0 => 0,
      _ => x * x * x,
    }
  }

  -- 3 explicit cases + default. Default path requires 3 inequality witnesses.
  pub fn multi_match(x: G) -> G {
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
  pub fn nested_match(x: G, y: G) -> G {
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
  pub fn match_poly_ops(x: G) -> (G, G) {
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
  pub fn match_lookup_ops(x: G) -> (G, G) {
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
  pub fn match_gadget_ops(i: G, j: G) -> (G, G, G) {
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
  pub fn match_gadget_ops_multi(i: G, j: G) -> ((G, G), [G; 8]) {
    match 0 {
      0 => (u8_add(i, j), u8_bit_decomposition(i)),
      1 => (u8_add(i, j), u8_bit_decomposition(i)),
    }
  }

  ---------------------------------------------------------------------------
  -- EqZero: both constant (degree 0, no constraints) and non-constant
  -- (degree 1, two constraints: sel * a * x = 0, sel * (a*d + x - 1) = 0)
  ---------------------------------------------------------------------------
  pub fn eq_zero_dummy(a: G, b: G) -> [G; 4] {
    let c = 0;
    let d = 101;
    [eq_zero(a), eq_zero(b), eq_zero(c), eq_zero(d)]
  }

  ---------------------------------------------------------------------------
  -- Memory: store/load
  ---------------------------------------------------------------------------
  pub fn store_and_load(x: G) -> G {
    load(store(x))
  }

  ---------------------------------------------------------------------------
  -- Enum with 2 constructors, pointer patterns, mutual recursion
  ---------------------------------------------------------------------------
  enum Nat {
    Zero,
    Succ(&Nat)
  }

  pub fn pointer_match() -> G {
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

  pub fn is_0_even() -> G {
    even(Nat.Zero)
  }

  pub fn is_1_even() -> G {
    even(Nat.Succ(store(Nat.Zero)))
  }

  pub fn is_2_even() -> G {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
  }

  pub fn is_0_odd() -> G {
    odd(Nat.Zero)
  }

  pub fn is_1_odd() -> G {
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

  pub fn shape_area(s: Shape) -> G {
    match s {
      Shape.Circle(r) => r * r,
      Shape.Rect(w, h) => w * h,
      Shape.Tri(a, b, c) => a + b + c,
    }
  }

  ---------------------------------------------------------------------------
  -- Constrained and unconstrained recursion
  ---------------------------------------------------------------------------
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }

  pub fn fibonacci(n: G) -> G {
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

  pub fn unconstrained_fibonacci(n: G) -> G {
    match n {
      0 => 1,
      _ =>
        let n_minus_1 = n - 1;
        match n_minus_1 {
          0 => 1,
          _ =>
            let n_minus_2 = n_minus_1 - 1;
            #fibonacci(n_minus_2) + unconstrained_fibonacci(n_minus_1),
        },
    }
  }

  ---------------------------------------------------------------------------
  -- Data structure compilation: proj, get, slice, set, destructuring
  ---------------------------------------------------------------------------
  pub fn projections(as: (G, G, G, G, G)) -> (G, G) {
    (proj(as, 1), proj(as, 3))
  }

  pub fn slice_and_get(as: [G; 5]) -> [G; 2] {
    let left = as[0 .. 2];
    let right = as[3 .. 5];
    [left[1], right[0]]
  }

  pub fn deconstruct_tuple(as: (G, G, G, G, G)) -> (G, G) {
    let (_, b, _, d, _) = as;
    (b, d)
  }

  pub fn deconstruct_array(as: [G; 5]) -> [G; 2] {
    let [_, b, _, d, _] = as;
    [b, d]
  }

  pub fn array_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    set(arr, 1, (0, 0))
  }

  -- proj on mixed-size tuple: offset arithmetic with non-uniform element sizes
  pub fn proj_mixed(t: (G, (G, G), G)) -> (G, G) {
    proj(t, 1)
  }

  -- get at last index + set at first index with eltSize=2: boundary cases
  pub fn array_get_set(arr: [(G, G); 3]) -> [(G, G); 3] {
    let p = arr[2];
    set(arr, 0, p)
  }

  ---------------------------------------------------------------------------
  -- Assertion
  ---------------------------------------------------------------------------
  pub fn assert_eq_trivial() {
    assert_eq!([1, 2, 3], [1, 2, 3]);
  }

  ---------------------------------------------------------------------------
  -- IO
  ---------------------------------------------------------------------------
  pub fn read_write_io() {
    let (idx, len) = io_get_info([0]);
    let xs: [G; 4] = io_read(idx, 4);
    io_write(xs);
    io_set_info([1], idx, len + 4);
  }

  ---------------------------------------------------------------------------
  -- Byte operations
  ---------------------------------------------------------------------------
  pub fn shr_shr_shl_decompose(byte: G) -> [G; 8] {
    let byte_shr = u8_shift_right(byte);
    let byte_shr_shr = u8_shift_right(byte_shr);
    let byte_shr_shr_shl = u8_shift_left(byte_shr_shr);
    u8_bit_decomposition(byte_shr_shr_shl)
  }

  pub fn u8_add_xor(i: G, j: G) -> ((G, G), (G, G)) {
    let i_xor_j = u8_xor(i, j);
    (u8_add(i_xor_j, i), u8_add(i_xor_j, j))
  }

  pub fn u8_sub_function(i: G, j: G) -> (G, G) {
    u8_sub(i, j)
  }

  pub fn u8_less_than_function(i: G, j: G) -> G {
    u8_less_than(i, j)
  }

  pub fn u8_and_function(i: G, j: G) -> G {
    u8_and(i, j)
  }

  pub fn u8_or_function(i: G, j: G) -> G {
    u8_or(i, j)
  }

  ---------------------------------------------------------------------------
  -- u32 comparison
  ---------------------------------------------------------------------------
  pub fn u32_less_than_function(x: G, y: G) -> G {
    u32_less_than(x, y)
  }

  ---------------------------------------------------------------------------
  -- Fold/iteration
  ---------------------------------------------------------------------------
  pub fn fold_matrix_sum(m: [[G; 2]; 2]) -> G {
    fold(0 .. 2, 0, |acc_outer, @i|
      fold(0 .. 2, acc_outer, |acc_inner, @j|
        acc_inner + m[@i][@j]
      )
    )
  }

  ---------------------------------------------------------------------------
  -- Type aliases: basic, nested, in patterns
  ---------------------------------------------------------------------------
  type U8 = G
  type U16 = (U8, U8)
  type U32 = (U16, U16)
  type U64 = [U8; 8]
  type Pair = (U8, U8)

  pub fn alias_conversion(x: U64) -> U32 {
    ((x[0], x[1]), (x[2], x[3]))
  }

  ---------------------------------------------------------------------------
  -- EqZero degree-tracking regression: non-constant eq_zero followed by a
  -- constant and then a degree-2 multiplication chain. The layout must push
  -- exactly 1 degree entry for eq_zero (the boolean result); pushing 2
  -- (one phantom for the internal inverse witness) desynchronises the degree
  -- array from bytecode value indices, causing the layout to under-count
  -- auxiliary columns and the circuit builder to access out-of-bounds columns.
  ---------------------------------------------------------------------------
  pub fn eq_zero_degree_desync(x: G) -> G {
    let a = eq_zero(x);
    let b = 100;
    let c = x * x;
    let d = c * c;
    a + b + d
  }

  ---------------------------------------------------------------------------
  -- Templates: parametric datatypes and functions
  ---------------------------------------------------------------------------
  enum Wrapper‹A› {
    Mk(A)
  }

  fn unwrap‹A›(w: Wrapper‹A›) -> A {
    match w {
      Wrapper.Mk(x) => x,
    }
  }

  pub fn template_basic() -> G {
    let w = Wrapper.Mk(42);
    unwrap(w)
  }

  enum Option‹A› {
    Some(A),
    None
  }

  fn unwrap_or‹A›(opt: Option‹A›, default: A) -> A {
    match opt {
      Option.Some(x) => x,
      Option.None => default,
    }
  }

  pub fn template_unwrap_some() -> G {
    let opt = Option.Some(42);
    unwrap_or(opt, 0)
  }

  pub fn template_unwrap_none() -> G {
    let opt = Option.None;
    unwrap_or(opt, 99)
  }

  enum TPair‹A, B› {
    Mk(A, B)
  }

  fn tpair_first‹A, B›(p: TPair‹A, B›) -> A {
    match p {
      TPair.Mk(a, _) => a,
    }
  }

  fn tpair_second‹A, B›(p: TPair‹A, B›) -> B {
    match p {
      TPair.Mk(_, b) => b,
    }
  }

  pub fn template_pair() -> (G, G) {
    let p = TPair.Mk(10, 20);
    (tpair_first(p), tpair_second(p))
  }

  -- Nested templates: Option‹TPair‹G, G››
  pub fn template_nested() -> G {
    let inner = TPair.Mk(3, 4);
    let opt = Option.Some(inner);
    let p = unwrap_or(opt, TPair.Mk(0, 0));
    tpair_first(p) + tpair_second(p)
  }

  ---------------------------------------------------------------------------
  -- Non-tail match: exercises basic, early return, sequential, and nested
  -- cases. All paths tested via a single entry point to minimise proof count.
  ---------------------------------------------------------------------------

  fn ntm_basic(a: G) -> G {
    let y = match a { 0 => 100, 1 => 200, _ => a * a, };
    y + 1
  }
  fn ntm_early_ret(a: G) -> G {
    let y = match a { 0 => return 999, _ => a + a, };
    y * y
  }
  fn ntm_sequential(a: G, b: G) -> G {
    let x = match a { 0 => 1, 1 => 2, _ => a, };
    let y = match b { 0 => 10, 1 => 20, _ => b, };
    x + y
  }
  fn ntm_nested(a: G, b: G) -> G {
    let x = match a {
      0 => match b { 0 => return 0, _ => 42, },
      _ => 99,
    };
    x + 1
  }
  -- Pre-branch constant multiplied in a branch (no default).
  -- c has degree 0; exposes sharedAux over-count when all branches are
  -- explicit field cases (no inverse-witness auxiliaries to mask the gap).
  fn ntm_const_mul(a: G) -> G {
    let c = 5;
    let x = match a { 0 => c * c, 1 => c * c * c, };
    x + 1
  }
  -- Non-tail match returning a tuple (multi-output merge)
  fn ntm_tuple(a: G) -> (G, G) {
    let (x, y) = match a { 0 => (10, 20), 1 => (30, 40), _ => (a, a * a), };
    (x + 1, y + 1)
  }

  -- Non-tail match followed by a tail match (continuation is itself a match)
  fn ntm_then_tail_match(a: G, b: G) -> G {
    let x = match a { 0 => 100, _ => a, };
    match b { 0 => x, _ => x + b, }
  }

  -- Non-tail match with function calls in branches
  fn ntm_helper(x: G) -> G { x * x + 1 }
  fn ntm_call_in_branch(a: G) -> G {
    let x = match a { 0 => ntm_helper(5), _ => ntm_helper(a), };
    x + 1
  }

  -- Non-tail match with store/load in branches (lookup gating)
  fn ntm_store_load(a: G) -> G {
    let x = match a { 0 => load(store(42)), _ => load(store(a)), };
    x + 1
  }

  -- Refutable pattern destructuring in a let (like `let Nat.Succ(&x) = n;`)
  fn ntm_ctor_let(n: Nat) -> G {
    let Nat.Succ(&inner) = n;
    match inner { Nat.Zero => 1, Nat.Succ(_) => 2, }
  }

  -- Refutable pattern let with a stored enum (Shape through pointer)
  fn ntm_shape_let() -> G {
    let s = store(Shape.Rect(3, 4));
    let Shape.Rect(w, h) = load(s);
    w + h
  }

  -- Large match (8 branches, no default) — like const_num_levels
  fn ntm_large(a: G) -> G {
    let x = match a {
      0 => 10, 1 => 20, 2 => 30, 3 => 40,
      4 => 50, 5 => 60, 6 => 70, 7 => 80,
    };
    x + 1
  }

  -- Non-tail match where one branch has a lookup (store) and another doesn't,
  -- followed by a continuation that also does a lookup. Tests sharedLookups.
  fn ntm_mixed_lookups(a: G) -> G {
    let x = match a {
      0 => 42,
      _ => load(store(a)),
    };
    load(store(x + 1))
  }

  -- Non-tail match where branches call different functions with different
  -- lookup counts. Replicates the IxVM get_constant_info_by_variant pattern.
  fn ntm_heavy_calls(a: G) -> G { load(store(load(store(a)))) }
  fn ntm_light_calls(a: G) -> G { a + 1 }
  fn ntm_asymmetric_lookups(a: G, b: G) -> G {
    let x = match a {
      0 => ntm_heavy_calls(b),
      1 => ntm_light_calls(b),
      _ => b,
    };
    load(store(x))
  }

  -- Non-tail match inside a tail match branch (like get_constant_info)
  -- Minimal reproducer: non-tail match inside a tail match branch
  fn ntm_inside_tail_match(flag: G, a: G) -> G {
    match flag {
      0 =>
        let x = match a { 0 => 100, 1 => 200, };
        x + 1,
      _ => a,
    }
  }

  -- Explicit branches heavier than default: CKind.B and CKind.E have
  -- pointer derefs (&Nat) that generate load ops, making those branches
  -- use more auxiliaries than CKind.A/C/D/F. When the match compiler
  -- places a light branch as the default, the default has fewer auxiliaries
  -- than the heavy explicit branches. This catches the bug where
  -- Ctrl::Match left state.column at the default's level, missing the
  -- explicit branches' higher water mark.
  fn ntm_heavy_explicit(flag: G, kind: CKind) -> G {
    match flag {
      0 =>
        let val = match kind {
          CKind.A(x) => x,
          CKind.B(x, &extra) =>
            match extra { Nat.Zero => x, Nat.Succ(_) => x + 10, },
          CKind.C(x) => x * x,
          CKind.D(x, y) => x + y,
          CKind.E(x, &extra) =>
            match extra { Nat.Zero => x * x, Nat.Succ(_) => x + 100, },
          CKind.F(x) => x,
        };
        val + 1,
      _ => 0,
    }
  }

  -- Replicates const_num_levels: 8-branch non-tail match (no default)
  -- inside a many-branch outer tail match
  fn ntm_large_inside_tail(outer: G, inner: G) -> G {
    match outer {
      0 => inner,
      1 => inner + 1,
      2 =>
        let x = match inner {
          0 => 10, 1 => 20, 2 => 30, 3 => 40,
          4 => 50, 5 => 60, 6 => 70, 7 => 80,
        };
        x + 1,
      _ => inner * inner,
    }
  }

  -- Replicates rec_rule_first_ctor: refutable pattern let with pointer deref
  -- inside a deeply nested tail match. The `let` destructures a stored
  -- enum value through a pointer.
  fn ntm_refutable_let_in_match(flag: G) -> G {
    let list = store(Nat.Succ(store(Nat.Zero)));
    match flag {
      0 =>
        let Nat.Succ(&inner) = load(list);
        match inner { Nat.Zero => 42, _ => 99, },
      _ => 0,
    }
  }

  -- Replicates convert_all: matchContinue inside List.Cons branch,
  -- continuation has store + function call
  -- Replicates convert_all: recursive function with matchContinue inside
  -- a List.Cons branch, continuation stores + recurses
  -- Replicates convert_all: recursive list processing with a non-tail match
  -- in the Cons branch where branches call functions with different lookups
  -- Replicates convert_all pattern: recursive function with 6-branch
  -- non-tail match in the Cons branch. Each branch calls a different
  -- function with different lookup counts. Continuation stores + recurses.
  fn ntm_cv_a(x: G) -> G { x }
  fn ntm_cv_b(x: G) -> G { load(store(x)) }
  fn ntm_cv_c(x: G) -> G { let _ = store(x); load(store(x + 1)) }
  fn ntm_cv_d(x: G) -> G { x * x }
  fn ntm_cv_e(x: G) -> G { load(store(load(store(x)))) }
  fn ntm_cv_f(x: G, y: G) -> G { x + y }
  -- Replicates convert_all exactly: Cons branch with pointer derefs in
  -- the pattern, non-tail match with branches that have different arg
  -- counts (some with pointer derefs), continuation stores + recurses.
  -- 6-variant enum with pointer fields, matching convert_one's ConvertKind
  enum CKind {
    A(G),
    B(G, &Nat),
    C(G),
    D(G, G),
    E(G, &Nat),
    F(G)
  }
  fn ntm_cv_a2(x: G) -> G { x + 1 }
  fn ntm_cv_b2(x: G, extra: Nat) -> G {
    match extra { Nat.Zero => x, Nat.Succ(_) => x + 10, }
  }
  fn ntm_cv_c2(x: G) -> G { x * x }
  fn ntm_cv_d2(x: G, y: G) -> G { x + y }
  fn ntm_cv_e2(x: G, extra: Nat) -> G {
    match extra { Nat.Zero => x * x, Nat.Succ(_) => x + 100, }
  }
  fn ntm_cv_f2(x: G) -> G { load(store(x)) }
  fn ntm_convert_all(inputs: Nat, kind: CKind) -> G {
    match inputs {
      Nat.Zero => 0,
      Nat.Succ(&rest) =>
        let ci = match kind {
          CKind.A(x) => ntm_cv_a2(x),
          CKind.B(x, &extra) => ntm_cv_b2(x, extra),
          CKind.C(x) => ntm_cv_c2(x),
          CKind.D(x, y) => ntm_cv_d2(x, y),
          CKind.E(x, &extra) => ntm_cv_e2(x, extra),
          CKind.F(x) => ntm_cv_f2(x),
        };
        let _ = store(ci);
        ci + ntm_convert_all(rest, kind),
    }
  }

  fn ntm_recursive_test() -> G {
    let zero = Nat.Zero;
    let one = Nat.Succ(store(Nat.Zero));
    let two = Nat.Succ(store(Nat.Succ(store(Nat.Zero))));
    -- Exercise ALL 6 branches AND both Nil/Cons paths of the outer match.
    -- Multiple iterations to stress shared columns across many trace rows.
    let r1 = ntm_convert_all(two, CKind.A(10));
    let r2 = ntm_convert_all(one, CKind.B(5, store(Nat.Succ(store(Nat.Zero)))));
    let r3 = ntm_convert_all(two, CKind.C(3));
    let r4 = ntm_convert_all(one, CKind.D(2, 3));
    let r5 = ntm_convert_all(one, CKind.E(7, store(Nat.Zero)));
    let r6 = ntm_convert_all(two, CKind.F(4));
    -- Also call with zero iterations (Nil path only)
    let r7 = ntm_convert_all(zero, CKind.A(99));
    r1 + r2 + r3 + r4 + r5 + r6 + r7
  }

  fn ntm_tuple_sum(a: G) -> G {
    let (x, y) = ntm_tuple(a);
    x + y
  }
  pub fn non_tail_match() -> G {
    -- Basic, early return, sequential, nested, const mul
    let r1 = ntm_basic(0) + ntm_basic(5);
    let r2 = ntm_early_ret(0) + ntm_early_ret(3);
    let r3 = ntm_sequential(1, 1);
    let r4 = ntm_nested(0, 1) + ntm_nested(1, 0);
    let r5 = ntm_const_mul(0);
    -- Tuple output, tail-match continuation, calls/store in branches
    let r6 = ntm_tuple_sum(0);
    let r7 = ntm_then_tail_match(0, 3);
    let r8 = ntm_call_in_branch(0);
    let r9 = ntm_store_load(0);
    -- Large match, constructor patterns, mixed lookups
    let r10 = ntm_large(0);
    let r11 = ntm_ctor_let(Nat.Succ(store(Nat.Zero)));
    let r12 = ntm_mixed_lookups(0);
    let r13 = ntm_shape_let();
    let r14 = ntm_asymmetric_lookups(1, 10);
    -- matchContinue inside tail match (both branches exercised)
    let r15 = ntm_inside_tail_match(0, 0) + ntm_inside_tail_match(0, 1)
            + ntm_inside_tail_match(1, 5);
    -- Large match inside tail match (all outer+inner branches)
    let r16 = ntm_large_inside_tail(2, 0) + ntm_large_inside_tail(2, 3)
            + ntm_large_inside_tail(2, 7) + ntm_large_inside_tail(0, 5)
            + ntm_large_inside_tail(1, 5) + ntm_large_inside_tail(3, 4);
    -- Heavy explicit branches (pointer derefs heavier than default)
    let r17 = ntm_heavy_explicit(0, CKind.B(5, store(Nat.Succ(store(Nat.Zero)))))
            + ntm_heavy_explicit(0, CKind.A(7)) + ntm_heavy_explicit(1, CKind.A(99));
    -- Refutable pattern let
    let r18 = ntm_refutable_let_in_match(0);
    -- Recursive with all 6 branches + Nil path exercised
    let r19 = ntm_recursive_test();
    -- Nested early return (yields 0, sum unchanged)
    let r20 = ntm_nested(0, 0);
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10
    + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20
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
    .noIO `unconstrained_fibonacci #[6] #[13],

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
    { functionName := `read_write_io
      inputIOBuffer := ⟨#[1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩)]⟩
      expectedIOBuffer := ⟨#[1, 2, 3, 4, 1, 2, 3, 4], .ofList [(#[0], ⟨0, 4⟩), (#[1], ⟨0, 8⟩)]⟩ },

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

    -- Type aliases
    { AiurTestCase.noIO `alias_conversion #[1, 2, 3, 4, 5, 6, 7, 8] #[1, 2, 3, 4]
        with label := "alias_conversion (U64 = [U8; 8], U32 = (U16, U16))" },

    -- EqZero degree-tracking regression (eq_zero(3)=0, 100, 3*3=9, 9*9=81, 0+100+81=181)
    .noIO `eq_zero_degree_desync #[3] #[181],

    -- Templates
    .noIO `template_basic #[] #[42],
    .noIO `template_unwrap_some #[] #[42],
    .noIO `template_unwrap_none #[] #[99],
    .noIO `template_pair #[] #[10, 20],
    .noIO `template_nested #[] #[7],

    -- Non-tail match: all patterns in one proof
    .noIO `non_tail_match #[] #[2281],
  ]

end
