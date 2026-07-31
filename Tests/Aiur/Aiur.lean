module

public import Tests.Aiur.Common
public import Ix.Aiur.Meta

public section

open LSpec

-- The PROVING corpus: only functions reachable from the proving cases in
-- `aiurTestCases` below live here — every function compiles to a circuit
-- that every proof commits (empty or not). Execution/interpreter coverage
-- for frontend constructs (data-structure layout, templates, aliases,
-- single-op wrappers, …) lives in `aiur-cross` (`Tests/Aiur/Cross.lean`).
def toplevel := ⟦
  -- Callee for match_lookup_ops and inline_test
  pub fn id(n: G) -> G {
    n
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
  pub fn match_gadget_ops(i: U8, j: U8) -> (U8, U8, G) {
    match 0 {
      0 => (u8_shift_right(i), u8_xor(i, j), u32_less_than(to_field(i), to_field(j))),
      1 => (u8_shift_right(i), u8_xor(i, j), u32_less_than(to_field(j), to_field(i))),
    }
  }

  ---------------------------------------------------------------------------
  -- Active/inactive sel-gating: multi-output gadget lookups
  --
  -- u8_add has output_size=2, testing the same missing-sel bug in
  -- bytes2_constraints for the multi-output case. u8_bit_decomposition has
  -- output_size=8, testing it for bytes1_constraints.
  ---------------------------------------------------------------------------
  pub fn match_gadget_ops_multi(i: U8, j: U8) -> ((U8, U8), [G; 8]) {
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
  -- Enum with 2 constructors, pointer patterns, mutual recursion
  ---------------------------------------------------------------------------
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

  pub fn is_2_even() -> G {
    even(Nat.Succ(store(Nat.Succ(store(Nat.Zero)))))
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
  -- IO
  ---------------------------------------------------------------------------
  -- Exercises channel disambiguation: same key #[0] on channels 0 and 1
  -- resolves to distinct (idx, len) and arenas. Reads from each, writes
  -- the concatenation back to channel 2, and registers `[1]` on channel 0.
  pub fn read_write_io() {
    let (idx_a, len_a) = io_get_info(0, [0]);
    let (idx_b, _len_b) = io_get_info(1, [0]);
    let xs: [G; 4] = io_read(0, idx_a, 4);
    let ys: [G; 4] = io_read(1, idx_b, 4);
    io_write(2, xs);
    io_write(2, ys);
    io_set_info(0, [1], idx_a, len_a + 4);
  }

  ---------------------------------------------------------------------------
  -- Byte operations
  ---------------------------------------------------------------------------
  pub fn shr_shr_shl_decompose(byte: U8) -> [G; 8] {
    let byte_shr = u8_shift_right(byte);
    let byte_shr_shr = u8_shift_right(byte_shr);
    let byte_shr_shr_shl = u8_shift_left(byte_shr_shr);
    u8_bit_decomposition(byte_shr_shr_shl)
  }

  pub fn u8_add_xor(i: U8, j: U8) -> ((U8, U8), (U8, U8)) {
    let i_xor_j = u8_xor(i, j);
    (u8_add(i_xor_j, i), u8_add(i_xor_j, j))
  }

  -- Full u32 right-rotation by 7, built by chaining the partial gadget over
  -- adjacent little-endian byte pairs (2 lookups + 2 free field adds).
  pub fn u32_rotr7(b: [U8; 4]) -> [U8; 4] {
    let [b0, b1, b2, b3] = b;
    let (a0, a1, a2) = u8_chain_rotr7(b0, b1);
    let (c0, c1, c2) = u8_chain_rotr7(b2, b3);
    -- The two combined parts occupy disjoint bit positions, so their sum never
    -- overflows a byte: add cheaply as `G`, then reinterpret as `U8`.
    [a0, u8_from_field_unsafe(to_field(a1) + to_field(c2)), c0,
     u8_from_field_unsafe(to_field(c1) + to_field(a2))]
  }

  ---------------------------------------------------------------------------
  -- u32 comparison
  ---------------------------------------------------------------------------
  pub fn u32_less_than_function(x: G, y: G) -> G {
    u32_less_than(x, y)
  }

  ---------------------------------------------------------------------------
  -- u8 range-check / to_field
  ---------------------------------------------------------------------------
  pub fn range_check_id(a: G, b: G) -> (G, G) {
    let (x, y) = u8_range_check(a, b);
    (to_field(x), to_field(y))
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

  -- Non-tail match whose scrutinee is a function call (`let x = match foo(bar) {...}`).
  -- The scrutinee is hoisted into a fresh let by the match compiler; the
  -- continuation must still reach `matchContinue`. ntm_helper(x) = x*x+1,
  -- so a=0 -> 1 -> 100 -> 101.
  fn ntm_match_on_call(a: G) -> G {
    let x = match ntm_helper(a) { 1 => 100, 5 => 200, _ => a * a, };
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
  fn ntm_cv_c(x: G) -> G { store(x); load(store(x + 1)) }
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
        store(ci);
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
    -- Function-call scrutinee: 101 + 201 + 10 = 312
    let r21 = ntm_match_on_call(0) + ntm_match_on_call(2) + ntm_match_on_call(3);
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10
    + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20 + r21
  }

  ---------------------------------------------------------------------------
  -- Inlined function calls (`@fn(args)`)
  --
  -- An `@`-call splices the callee's body into the caller's circuit: no
  -- separate circuit, no call interface. These cases cover the splice in
  -- every position lowering treats specially (let-RHS, strict argument
  -- slots), plus alpha-renaming, nesting, branching callees, gadget
  -- lookups joining the caller, and mixing inlined with normal calls.
  ---------------------------------------------------------------------------

  fn inl_double(x: G) -> G {
    let t = x + x;
    t
  }

  fn inl_sq(x: G) -> G { x * x }

  -- Callee that itself @-inlines another helper (nested splice)
  fn inl_sq_plus(x: G, y: G) -> G { @inl_sq(x) + y }

  -- Multi-output callee
  fn inl_pair(x: G) -> (G, G) { (x + 1, x * 2) }

  -- Branching callee: tail match spliced into a let-RHS position
  fn inl_sign(x: G) -> G {
    match x {
      0 => 0,
      _ => 1,
    }
  }

  -- Gadget lookup inside the callee
  fn inl_add8(a: U8, b: U8) -> (U8, U8) { u8_add(a, b) }

  -- Single aggregate entry: every scenario in one circuit/proof.
  pub fn inline_test() -> G {
    -- Basic splice
    let r1 = @inl_double(21);                     -- 42
    -- Nested splice (callee @-inlines another helper)
    let r2 = @inl_sq_plus(3, 4);                  -- 13
    -- Capture safety: caller binds `t` (the callee's local name) and the
    -- argument mentions it
    let t = 5;
    let r3 = @inl_double(t + 1) + t;              -- 17
    -- Strict positions: array elements, operator operands, call argument
    let arr = [@inl_double(3), @inl_sq(3)];       -- [6, 9]
    let r4 = arr[0] + arr[1] * 100;               -- 906
    let r5 = @inl_double(3) + @inl_sq(3);         -- 15
    let r6 = id(@inl_double(7));                  -- 14
    -- Multi-output callee
    let (p1, p2) = @inl_pair(5);                  -- (6, 10)
    let r7 = p1 + p2 * 100;                       -- 1006
    -- Branching callee in operand position, both paths (the spliced match
    -- gets bound to a fresh local before hoisting)
    let r8 = @inl_sign(0) + @inl_sign(5) * 100;   -- 100
    -- Same callee inlined and normally called: the normal call keeps its
    -- own circuit + lookup, the inlined one joins this circuit
    let r9 = @inl_sq(3) + inl_sq(4);              -- 25
    -- Gadget lookup in the callee joins this circuit
    let (s, c) = @inl_add8(200u8, 100u8);         -- (44, 1)
    let r10 = to_field(s) + to_field(c) * 1000;   -- 1044
    r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10
  }

  ---------------------------------------------------------------------------
  -- Unconstrained big-uint div/mod: lists of [U8; 8] limbs in, the same
  -- list datatype at [G; 8] out. The datatype must declare Cons FIRST
  -- (runtime tag contract: 0 = Cons, 1 = Nil). Limbs are little-endian
  -- u64s, head-first.
  ---------------------------------------------------------------------------
  enum BNode‹T› {
    BCons(T, &BNode‹T›),
    BNil
  }

  fn blist0() -> &BNode‹[U8; 8]› { store(BNode.BNil) }
  fn blist1(l: [U8; 8]) -> &BNode‹[U8; 8]› { store(BNode.BCons(l, blist0())) }
  fn blist2(l0: [U8; 8], l1: [U8; 8]) -> &BNode‹[U8; 8]› {
    store(BNode.BCons(l0, blist1(l1)))
  }

  -- u64 value of the first result limb (fits in G for the cases below).
  fn glimb_val(p: &BNode‹[G; 8]›) -> G {
    match load(p) {
      BNode.BCons(l, _) => l[0] + 256 * l[1] + 65536 * l[2] + 16777216 * l[3]
        + 4294967296 * l[4] + 1099511627776 * l[5] + 281474976710656 * l[6]
        + 72057594037927936 * l[7],
      BNode.BNil => 0,
    }
  }

  fn glist_is_nil(p: &BNode‹[G; 8]›) -> G {
    match load(p) {
      BNode.BNil => 1,
      BNode.BCons(_, _) => 0,
    }
  }

  -- Aggregate: plain divide (300/7), unit divisor (300/1), zero divisor
  -- (300/0 → (Nil, 300) by convention), and a two-limb dividend with a
  -- Nil remainder (2^64 / 2 → (2^63, Nil), canonical single-limb q).
  pub fn divmod_test() -> G {
    let a300 = blist1([44u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let b7 = blist1([7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let (q1, r1) = unconstrained_big_uint_div_mod(a300, b7);
    let s1 = glimb_val(q1) + 1000 * glimb_val(r1);          -- 42 + 6000
    let b1 = blist1([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let (q2, _r2) = unconstrained_big_uint_div_mod(a300, b1);
    let s2 = glimb_val(q2);                                 -- 300
    let (q3, r3) = unconstrained_big_uint_div_mod(a300, blist0());
    let s3 = 1000000 * glist_is_nil(q3) + glimb_val(r3);    -- 1000300
    let a64 = blist2([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                     [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let b2 = blist1([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let (q4, r4) = unconstrained_big_uint_div_mod(a64, b2);
    let s4 = glimb_val(q4) + glist_is_nil(r4);              -- 2^63 + 1
    s1 + s2 + s3 + s4
  }

  ---------------------------------------------------------------------------
  -- Unconstrained field hints: `g_to_bytes` returns the 8 LE bytes of the
  -- CANONICAL u64 value as raw [G; 8] advice; `g_inverse` the field
  -- inverse with 0 ↦ 0.
  ---------------------------------------------------------------------------
  pub fn hint_test() -> G {
    -- 300 = 0x012C → LE bytes [44, 1, 0, ...]
    let b = unconstrained_g_to_bytes(300);
    let s1 = b[0] + 1000 * b[1];                -- 1044
    let s2 = b[7];                              -- 0
    -- x * x⁻¹ = 1 for x ≠ 0; 0 ↦ 0
    let s3 = unconstrained_g_inverse(7) * 7;    -- 1
    let s4 = unconstrained_g_inverse(0);        -- 0
    -- Canonicality: 0 - 1 wraps to p - 1 = 0xFFFFFFFF00000000
    let c = unconstrained_g_to_bytes(0 - 1);
    let s5 = c[4] + c[0];                       -- 255
    s1 + s2 + 10 * s3 + s4 + s5                 -- 1309
  }

  ---------------------------------------------------------------------------
  -- Grouped circuits (`CompiledToplevel.groupFunctions`): the test runner
  -- groups these three into one circuit whose branching selects the member.
  -- Grouping is a circuit-level choice, so there is NO source annotation:
  -- the same functions also run ungrouped in the plain suite. Members
  -- differ in arity, output and branch count, call each other (through the
  -- shared circuit) and recurse.
  ---------------------------------------------------------------------------
  fn grouped_double(x: G) -> G {
    x + x
  }

  -- Different arity, a match (two selectors), calls a fellow group member.
  fn grouped_pick(t: G, a: G, b: G) -> G {
    match t {
      0 => grouped_double(a),
      _ => b,
    }
  }

  -- Recursive group member: self-calls route through the shared circuit.
  fn grouped_sum_range(n: G) -> G {
    match n {
      0 => 0,
      _ => n + grouped_sum_range(n - 1),
    }
  }

  pub fn calls_grouped(t: G, a: G, b: G) -> G {
    grouped_pick(t, a, b) + grouped_sum_range(a)
  }
⟧

/-- The PROVING suite: every case runs the full prove+verify pipeline
    (plus execute and interpret, which come for free in `runTestCase`).
    A case belongs here only when it pins a distinct constraint,
    selector-gating, or lookup-argument configuration — the things
    execution never evaluates. Execution-semantics coverage (compiler,
    evaluators, interpreter) lives in `aiur-cross`
    (`Tests/Aiur/Cross.lean`). When several inputs of the same function
    differ only in which path is active, only a minimal covering set of
    proofs is kept — the other paths run in `aiur-cross`. -/
def aiurTestCases : List AiurTestCase := [
    -- Match: 1 explicit case + default, prove both paths (each side gates
    -- the other's constraints)
    .prove `match_mul #[0] #[0] (label := "match_mul(0)"),
    .prove `match_mul #[2] #[8] (label := "match_mul(2)"),

    -- Match: 3 explicit cases + default. Prove one explicit path and the
    -- default path (3 inequality witnesses); the remaining explicit paths
    -- exercise the same witness layout
    .prove `multi_match #[0] #[100] (label := "multi_match(0)"),
    .prove `multi_match #[5] #[25] (label := "multi_match(5)"),

    -- Nested match: 4 leaf selectors. Prove one explicit-explicit and one
    -- default-default leaf (witnesses at both nesting levels); the two
    -- mixed leaves repeat those layouts
    .prove `nested_match #[0, 0] #[10] (label := "nested_match(0,0)"),
    .prove `nested_match #[2, 3] #[5] (label := "nested_match(2,3)"),

    -- Sel-gating: polynomial constraints (Mul, EqZero, AssertEq).
    -- Inactive branch has assert_eq!(0,1) (fails without sel=0),
    -- different Mul (aux mismatch), different EqZero (witness mismatch).
    -- x=0 chosen so inactive EqZero constraint `sel*(x+1)*x_result =
    -- sel*1*1 = sel` is nonzero without gating.
    .prove `match_poly_ops #[0] #[0, 1],

    -- Sel-gating: function and memory lookup multiplicity
    .prove `match_lookup_ops #[42] #[42, 42],

    -- Sel-gating: gadget lookups (Bytes1, Bytes2) and U32LessThan polynomial
    -- constraints (swapped args on inactive path create decomposition mismatch)
    .prove `match_gadget_ops #[45, 131] #[22, 174, 1],

    -- Sel-gating: multi-output gadget lookups (Bytes2 output_size=2,
    -- Bytes1 output_size=8). Guards against partial fixes that only
    -- address output_size=1.
    .prove `match_gadget_ops_multi #[45, 131] #[176, 0, 1, 0, 1, 1, 0, 1, 0, 0],

    -- EqZero: constant path (c=0, d=101) and non-constant path (a=0, b=37)
    .prove `eq_zero_dummy #[0, 37] #[1, 0, 1, 0],

    -- Mutual recursion: prove only the deepest case (cross-circuit
    -- lookups through both functions); shallower depths are sub-traces
    .prove `is_2_even #[] #[1],

    -- 3-constructor enum: tag dispatch, field extraction at varying offsets,
    -- padding. Circle and Rect have degree-2 Mul in different branches with
    -- different operands sharing aux columns (implicit sel-gating test).
    -- Circle and Rect are the degree-2 pair sharing aux columns (the
    -- implicit sel-gating test): prove both. Tri (addition only) runs in
    -- aiur-cross.
    -- Circle(5): [tag=0, r=5, pad, pad] → 5*5 = 25
    .prove `shape_area #[0, 5, 0, 0] #[25] (label := "shape_area(Circle(5))"),
    -- Rect(3,4): [tag=1, w=3, h=4, pad] → 3*4 = 12
    .prove `shape_area #[1, 3, 4, 0] #[12] (label := "shape_area(Rect(3,4))"),

    -- Constrained recursion
    .prove `factorial #[5] #[120] (label := "factorial(5)"),

    -- Fibonacci: prove the deep case (call-lookup multiplicities > 1)
    .prove `fibonacci #[6] #[13] (label := "fibonacci(6)"),

    -- Unconstrained recursion: mixed constrained/unconstrained calls
    .prove `unconstrained_fibonacci #[6] #[13],

    -- IO
    { functionName := `read_write_io
      inputIOBuffer :=
        ⟨.ofList [(0, #[1, 2, 3, 4]), (1, #[5, 6, 7, 8])],
         .ofList [((0, #[0]), ⟨0, 4⟩), ((1, #[0]), ⟨0, 4⟩)]⟩
      expectedIOBuffer :=
        ⟨.ofList [(0, #[1, 2, 3, 4]),
                  (1, #[5, 6, 7, 8]),
                  (2, #[1, 2, 3, 4, 5, 6, 7, 8])],
         .ofList [((0, #[0]), ⟨0, 4⟩), ((1, #[0]), ⟨0, 4⟩),
                  ((0, #[1]), ⟨0, 8⟩)]⟩ },

    -- Byte operations: the gadget LOOKUP ARGUMENT (Bytes1/Bytes2
    -- multiplicities) is what proving checks; op results are table
    -- content, verified by execution. Prove one Bytes1 chain, one
    -- multi-output Bytes2 case, and the chain-gadget combination; the
    -- single-op wrappers repeat the same lookup mechanics in aiur-cross.
    .prove `shr_shr_shl_decompose #[87] #[0, 1, 0, 1, 0, 1, 0, 0],
    .prove `u8_add_xor #[45, 131] #[219, 0, 49, 1],
    .prove `u32_rotr7 #[45, 131, 200, 17] #[6, 145, 35, 90],

    -- u8 range-check: prove the boundary case (U8RangeCheck circuit op)
    .prove `range_check_id #[0, 255] #[0, 255],

    -- u32 comparison: prove strict-less and the equality edge (distinct
    -- carry-chain witnesses); a > b repeats the a = b carry layout
    .prove `u32_less_than_function #[300, 500] #[1]
      (label := "u32_less_than(300,500)"),
    .prove `u32_less_than_function #[500, 500] #[0]
      (label := "u32_less_than(500,500)"),

    -- EqZero degree-tracking regression (eq_zero(3)=0, 100, 3*3=9, 9*9=81, 0+100+81=181)
    .prove `eq_zero_degree_desync #[3] #[181],

    -- Non-tail match: all patterns in one proof (incl. function-call scrutinee)
    .prove `non_tail_match #[] #[2593],

    -- Inlined function calls (`@fn(args)`): all scenarios in one proof
    .prove `inline_test #[] #[3182],

    -- Unconstrained big-uint div/mod: all cases in one proof
    -- (6042 + 300 + 1000300 + 2^63 + 1)
    .prove `divmod_test #[] #[9223372036855782451],

    -- Unconstrained g_to_bytes / g_inverse hints: all cases in one proof
    .prove `hint_test #[] #[1309],

    -- Grouped-circuit member functions, run UNGROUPED here (the grouped
    -- variant runs in the grouped env; see `testGroups`).
    -- t=0 → grouped_double(5) + Σ1..5 = 10 + 15 = 25; t≠0 → 9 + Σ1..3 = 15.
    .prove `calls_grouped #[0, 5, 9] #[25]
      (label := "calls_grouped(0,5,9)"),
    .prove `calls_grouped #[1, 3, 9] #[15]
      (label := "calls_grouped(1,3,9)"),
  ]

/-- The grouping the `aiur` runner applies for the grouped environment. -/
def testGroups : Array (String × Array Lean.Name) :=
  #[("test_group", #[`grouped_double, `grouped_pick, `grouped_sum_range])]

def groupedTestCases : List AiurTestCase := [
  .prove `calls_grouped #[0, 5, 9] #[25]
    (label := "calls_grouped(0,5,9) [grouped]"),
  .prove `calls_grouped #[1, 3, 9] #[15]
    (label := "calls_grouped(1,3,9) [grouped]"),
]

/-- Structural checks on the grouped partition: the grouped circuit exists,
holds exactly its members, its layout follows the merge rule (max inputs,
summed selectors, max auxiliaries, max lookups), and every constrained
function lands in exactly one circuit. -/
def groupingStructureChecks (compiled : Aiur.CompiledToplevel) : TestSeq :=
  let t := compiled.bytecode
  let memberOf := fun (name : Lean.Name) => compiled.getFuncIdx name |>.get!
  let expectedMembers :=
    #[`grouped_double, `grouped_pick, `grouped_sum_range].map memberOf
  match t.circuits.find? (·.name == "test_group") with
  | none => test "test_group circuit exists" false
  | some c =>
    let layouts := c.members.map (t.functions[·]!.layout)
    let expected := layouts.foldl (init := (⟨0, 0, 0, 0⟩ : Aiur.Bytecode.FunctionLayout))
      Aiur.Bytecode.FunctionLayout.merge
    let allCircuitMembers := t.circuits.flatMap (·.members)
    let constrained := (Array.range t.functions.size).filter
      (t.functions[·]!.constrained)
    test "test_group circuit exists" true ++
    test "test_group members" (c.members == expectedMembers) ++
    test "test_group layout follows the merge rule"
      (c.layout.inputSize == expected.inputSize &&
       c.layout.selectors == expected.selectors &&
       c.layout.auxiliaries == expected.auxiliaries &&
       c.layout.lookups == expected.lookups) ++
    test "every constrained function is in exactly one circuit"
      (allCircuitMembers.qsort (· < ·) == constrained)

end
